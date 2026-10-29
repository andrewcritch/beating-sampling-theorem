import BstLean.Part268CellShard27Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13025_0 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (42035598124053 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (221315441291 / 10000000000000 : ℝ))
      (E := (cell13025 ⟨0, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (42035598124053 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (221315441291 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_1 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (4201815347121 / 5000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213158385663 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨1, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (4201815347121 / 5000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213158385663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_2 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (84001442450121 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213162414159 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨2, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (84001442450121 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213162414159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_3 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41983301367487 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (110658319551 / 5000000000000 : ℝ))
      (E := (cell13025 ⟨3, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41983301367487 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (110658319551 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_4 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (10491473470117 / 12500000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (221317038223 / 10000000000000 : ℝ))
      (E := (cell13025 ⟨4, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (10491473470117 / 12500000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (221317038223 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_5 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83896997492151 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276646799457 / 12500000000000 : ℝ))
      (E := (cell13025 ⟨5, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83896997492151 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276646799457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_6 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83862231892953 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276647304863 / 12500000000000 : ℝ))
      (E := (cell13025 ⟨6, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83862231892953 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276647304863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_7 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41913745463931 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106591201661 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨7, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41913745463931 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106591201661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_8 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83792774561583 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (221318641193 / 10000000000000 : ℝ))
      (E := (cell13025 ⟨8, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83792774561583 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (221318641193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_9 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83758082759007 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106595235791 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨9, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83758082759007 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106595235791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_10 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41861707742603 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (221319447273 / 10000000000000 : ℝ))
      (E := (cell13025 ⟨10, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41861707742603 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (221319447273 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_11 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (20922193176359 / 25000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106599239843 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨11, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (20922193176359 / 25000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106599239843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_12 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83654154385131 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (138325152523 / 6250000000000 : ℝ))
      (E := (cell13025 ⟨12, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83654154385131 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (138325152523 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_13 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83619560489909 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (442641295357 / 20000000000000 : ℝ))
      (E := (cell13025 ⟨13, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83619560489909 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (442641295357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_14 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83584990985563 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213210478213 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨14, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83584990985563 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213210478213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_15 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83550445838063 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213214508079 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨15, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83550445838063 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213214508079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_16 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83515925013557 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213218513223 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨16, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83515925013557 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213218513223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_17 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83481428478369 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (553305624597 / 25000000000000 : ℝ))
      (E := (cell13025 ⟨17, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83481428478369 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (553305624597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_18 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41723478099497 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276653315793 / 12500000000000 : ℝ))
      (E := (cell13025 ⟨18, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41723478099497 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (276653315793 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_19 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (83412508142101 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213230543139 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨19, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (83412508142101 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213230543139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13026_0 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (16814236373293 / 20000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442608137937 / 20000000000000 : ℝ))
      (E := (cell13026 ⟨0, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (16814236373293 / 20000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442608137937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_1 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (21009073141791 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213044715107 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨1, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (21009073141791 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213044715107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_2 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (21000357020311 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213048738477 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨2, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (21000357020311 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213048738477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_3 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (8396658837247 / 10000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (110652635513 / 5000000000000 : ℝ))
      (E := (cell13026 ⟨3, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (8396658837247 / 10000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (110652635513 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_4 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83931773404799 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106528377187 / 50000000000000 : ℝ))
      (E := (cell13026 ⟨4, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83931773404799 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106528377187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_5 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (10487122892797 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106530381419 / 50000000000000 : ℝ))
      (E := (cell13026 ⟨5, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (10487122892797 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106530381419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_6 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41931108774767 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (221306474319 / 10000000000000 : ℝ))
      (E := (cell13026 ⟨6, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41931108774767 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (221306474319 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_7 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83827476590793 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213068760723 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨7, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83827476590793 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213068760723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_8 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83792760230859 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213072764511 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨8, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83792760230859 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213072764511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_9 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83758068434621 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106538380669 / 50000000000000 : ℝ))
      (E := (cell13026 ⟨9, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83758068434621 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106538380669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_10 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41861700583577 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442616151547 / 20000000000000 : ℝ))
      (E := (cell13026 ⟨10, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41861700583577 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442616151547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_11 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83688758393711 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213084759989 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨11, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83688758393711 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213084759989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_12 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83654140079729 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276636096767 / 12500000000000 : ℝ))
      (E := (cell13026 ⟨12, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83654140079729 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276636096767 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_13 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83619546190823 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213092805967 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨13, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83619546190823 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213092805967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_14 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (20896244173197 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276637100357 / 12500000000000 : ℝ))
      (E := (cell13026 ⟨14, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (20896244173197 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276637100357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_15 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41775215775797 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (553275207057 / 25000000000000 : ℝ))
      (E := (cell13026 ⟨15, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41775215775797 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (553275207057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_16 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (20878977683347 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106552414463 / 50000000000000 : ℝ))
      (E := (cell13026 ⟨16, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (20878977683347 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106552414463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_17 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41740707102247 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213108809693 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨17, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41740707102247 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213108809693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_18 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (5215433870713 / 6250000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (138319552081 / 6250000000000 : ℝ))
      (E := (cell13026 ⟨18, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (5215433870713 / 6250000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (138319552081 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_19 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (83412493880799 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276639605723 / 12500000000000 : ℝ))
      (E := (cell13026 ⟨19, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (83412493880799 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276639605723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13027_0 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (16814233497407 / 20000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (221292707779 / 10000000000000 : ℝ))
      (E := (cell13027 ⟨0, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (16814233497407 / 20000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (221292707779 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_1 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (42018139097059 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212931098063 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨1, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (42018139097059 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212931098063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_2 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (3360056548583 / 4000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553233764611 / 25000000000000 : ℝ))
      (E := (cell13027 ⟨2, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (3360056548583 / 4000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553233764611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_3 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41983287006087 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (110646954153 / 5000000000000 : ℝ))
      (E := (cell13027 ⟨3, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41983287006087 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (110646954153 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_4 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83931759050869 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212943064233 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨4, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83931759050869 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212943064233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_5 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41948484397403 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (276618390709 / 12500000000000 : ℝ))
      (E := (cell13027 ⟨5, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41948484397403 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (276618390709 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_6 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83862203208319 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212951101111 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨6, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83862203208319 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212951101111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_7 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (10478432781991 / 12500000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212955113777 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨7, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (10478432781991 / 12500000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212955113777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_8 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83792745902337 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106479556373 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨8, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83792745902337 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106479556373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_9 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41879027056219 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212963104799 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨9, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41879027056219 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212963104799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_10 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41861693425651 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553241788637 / 25000000000000 : ℝ))
      (E := (cell13027 ⟨10, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41861693425651 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553241788637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_11 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83688744084187 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442594230429 / 20000000000000 : ℝ))
      (E := (cell13027 ⟨11, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83688744084187 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442594230429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_12 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41827062888263 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553243790421 / 25000000000000 : ℝ))
      (E := (cell13027 ⟨12, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41827062888263 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (553243790421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_13 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (5226220743371 / 6250000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106489565403 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨13, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (5226220743371 / 6250000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106489565403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_14 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (8358496240221 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212983181327 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨14, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (8358496240221 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212983181327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_15 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (2088760431683 / 2500000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212987144039 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨15, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (2088760431683 / 2500000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212987144039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_16 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41757948227707 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106495599253 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨16, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41757948227707 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106495599253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_17 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41740699966407 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212995174897 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨17, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41740699966407 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212995174897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_18 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (16689385533203 / 20000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212999194173 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨18, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (16689385533203 / 20000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2212999194173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_19 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (83412479621689 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213003202379 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨19, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (83412479621689 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213003202379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13028_0 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (10508894138727 / 12500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212813461541 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨0, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (10508894138727 / 12500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212813461541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_1 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (84036263823281 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553204369167 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨1, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (84036263823281 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553204369167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_2 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16800279870023 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553205357987 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨2, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16800279870023 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553205357987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_3 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16793311930817 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212825451511 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨3, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16793311930817 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212825451511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_4 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16786348939829 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212829485613 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨4, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16786348939829 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212829485613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_5 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41948477224721 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106416742079 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨5, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41948477224721 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106416742079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_6 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83862188869309 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553209363671 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨6, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83862188869309 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553209363671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_7 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41913723961633 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (442568292497 / 20000000000000 : ℝ))
      (E := (cell13028 ⟨7, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41913723961633 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (442568292497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_8 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41896365788009 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276605689333 / 12500000000000 : ℝ))
      (E := (cell13028 ⟨8, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41896365788009 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276605689333 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_9 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (10469754974057 / 12500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212849501969 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨9, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (10469754974057 / 12500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212849501969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_10 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (20930843134413 / 25000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (110642674447 / 5000000000000 : ℝ))
      (E := (cell13028 ⟨10, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (20930843134413 / 25000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (110642674447 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_11 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41844364888431 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212857539959 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨11, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41844364888431 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212857539959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_12 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83654111475521 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (221286154489 / 10000000000000 : ℝ))
      (E := (cell13028 ⟨12, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83654111475521 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (221286154489 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_13 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16723903519849 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553216377363 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨13, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16723903519849 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553216377363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_14 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83584948113829 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106434777729 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨14, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83584948113829 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106434777729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_15 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83550402985243 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106436785947 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨15, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83550402985243 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106436785947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_16 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16703176435927 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553219390937 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨16, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16703176435927 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553219390937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_17 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83481385663327 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (442576307153 / 20000000000000 : ℝ))
      (E := (cell13028 ⟨17, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83481385663327 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (442576307153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_18 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (1303858021919 / 1562500000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276610693839 / 12500000000000 : ℝ))
      (E := (cell13028 ⟨18, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (1303858021919 / 1562500000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276610693839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_19 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (83412465364771 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106444777319 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨19, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (83412465364771 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106444777319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13029_0 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (42035569367403 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106349920471 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨0, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (42035569367403 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106349920471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_1 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (21009062363663 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212703850923 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨1, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (21009062363663 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212703850923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_2 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (84001384987863 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212707858991 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨2, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (84001384987863 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212707858991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_3 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41983272649101 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106355936763 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨3, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41983272649101 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106355936763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_4 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83931730349627 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (221271584471 / 10000000000000 : ℝ))
      (E := (cell13029 ⟨4, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83931730349627 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (221271584471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_5 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83896940106283 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442543979251 / 20000000000000 : ℝ))
      (E := (cell13029 ⟨5, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83896940106283 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442543979251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_6 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83862174532503 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106361930947 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨6, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83862174532503 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106361930947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_7 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83827433592807 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212727864853 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨7, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83827433592807 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212727864853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_8 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83792717251901 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106365956119 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨8, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83792717251901 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106365956119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_9 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41879012737337 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553183973699 / 25000000000000 : ℝ))
      (E := (cell13029 ⟨9, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41879012737337 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553183973699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_10 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83723358226201 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106369967571 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨10, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83723358226201 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106369967571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_11 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (10461089433967 / 12500000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (276592990429 / 12500000000000 : ℝ))
      (E := (cell13029 ⟨11, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (10461089433967 / 12500000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (276592990429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_12 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41827048588357 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553186980939 / 25000000000000 : ℝ))
      (E := (cell13029 ⟨12, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41827048588357 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553186980939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_13 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (40829835599 / 48828125000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212751941903 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨13, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (40829835599 / 48828125000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212751941903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_14 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (20896233456911 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212755925249 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨14, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (20896233456911 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212755925249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_15 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83550388705361 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212759937219 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨15, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83550388705361 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212759937219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_16 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83515867906049 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (221276398287 / 10000000000000 : ℝ))
      (E := (cell13029 ⟨16, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83515867906049 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (221276398287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_17 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (83481371396033 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (276595993817 / 12500000000000 : ℝ))
      (E := (cell13029 ⟨17, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (83481371396033 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (276595993817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_18 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (5215431196363 / 6250000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (110638598059 / 5000000000000 : ℝ))
      (E := (cell13029 ⟨18, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (5215431196363 / 6250000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (110638598059 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_19 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (20853112777511 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212775960849 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨19, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (20853112777511 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212775960849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13030_0 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (16814224872401 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106293136917 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨0, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (16814224872401 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106293136917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_1 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (10504529386029 / 12500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553147569673 / 25000000000000 : ℝ))
      (E := (cell13030 ⟨1, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (10504529386029 / 12500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553147569673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_2 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (42000685313909 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106297140843 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨2, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (42000685313909 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106297140843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_3 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (83966530944527 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (276574786399 / 12500000000000 : ℝ))
      (E := (cell13030 ⟨3, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (83966530944527 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (276574786399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_4 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (16786343200463 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (442520451479 / 20000000000000 : ℝ))
      (E := (cell13030 ⟨4, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (16786343200463 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (442520451479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_5 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (5243557860333 / 6250000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212606304007 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨5, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (5243557860333 / 6250000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212606304007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_6 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (838621601979 / 1000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212610322741 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨6, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (838621601979 / 1000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212610322741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_7 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (83827419264551 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212614320883 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨7, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (83827419264551 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212614320883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_8 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (16758540585997 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212618305469 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨8, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (16758540585997 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212618305469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_9 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41879005579547 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553155585333 / 25000000000000 : ℝ))
      (E := (cell13030 ⟨9, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41879005579547 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553155585333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_10 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (1674466878339 / 2000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106313159463 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨10, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (1674466878339 / 2000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106313159463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_11 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (10461087646101 / 12500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212630360663 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨11, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (10461087646101 / 12500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212630360663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_12 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (16730816576021 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553158589101 / 25000000000000 : ℝ))
      (E := (cell13030 ⟨12, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (16730816576021 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553158589101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_13 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (10452436127057 / 12500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (442527674003 / 20000000000000 : ℝ))
      (E := (cell13030 ⟨13, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (10452436127057 / 12500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (442527674003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_14 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (16716983908731 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (276580293609 / 12500000000000 : ℝ))
      (E := (cell13030 ⟨14, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (16716983908731 / 20000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (276580293609 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_15 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (83550374427673 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (5531615891 / 250000000000 : ℝ))
      (E := (cell13030 ⟨15, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (83550374427673 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (5531615891 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_16 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41757926817329 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106325198827 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨16, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41757926817329 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106325198827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_17 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (20870339282733 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553163590243 / 25000000000000 : ℝ))
      (E := (cell13030 ⟨17, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (20870339282733 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553163590243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_18 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (5215430305187 / 6250000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106329183657 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨18, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (5215430305187 / 6250000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106329183657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_19 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (20853109214377 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212662421013 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨19, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (20853109214377 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212662421013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13031_0 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (84071109991413 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106236351189 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨0, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (84071109991413 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106236351189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_1 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (4201811036201 / 5000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442495340423 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨1, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (4201811036201 / 5000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442495340423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_2 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (84001356269979 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442496140007 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨2, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (84001356269979 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442496140007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_3 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (2623953643533 / 3125000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106242352257 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨3, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (2623953643533 / 3125000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106242352257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_4 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83931701657207 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (276561090459 / 12500000000000 : ℝ))
      (E := (cell13031 ⟨4, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83931701657207 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (276561090459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_5 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41948455713289 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212492765373 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨5, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41948455713289 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212492765373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_6 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (167724291731 / 200000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106248360631 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨6, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (167724291731 / 200000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106248360631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_7 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (327450800541 / 390625000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212500772571 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨7, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (327450800541 / 390625000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212500772571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_8 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (8379268861027 / 10000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553126188097 / 25000000000000 : ℝ))
      (E := (cell13031 ⟨8, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (8379268861027 / 10000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553126188097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_9 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83757996845713 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212508783529 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨9, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83757996845713 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212508783529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_10 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83723329609897 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (69141023639 / 3125000000000 : ℝ))
      (E := (cell13031 ⟨10, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83723329609897 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (69141023639 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_11 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83688686868079 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442503358711 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨11, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83688686868079 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442503358711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_12 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83654068585693 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442504156943 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨12, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83654068585693 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442504156943 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_13 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (16723894945671 / 20000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212524793791 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨13, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (16723894945671 / 20000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212524793791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_14 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (4179245263093 / 5000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (221252882633 / 10000000000000 : ℝ))
      (E := (cell13031 ⟨14, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (4179245263093 / 5000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (221252882633 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_15 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83550360152179 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212532829439 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨15, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83550360152179 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212532829439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_16 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83515839365459 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106268404053 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨16, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83515839365459 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106268404053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_17 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (83481342868023 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442508165063 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨17, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (83481342868023 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442508165063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_18 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (1303857353537 / 1562500000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106272413689 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨18, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (1303857353537 / 1562500000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106272413689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_19 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41706211303581 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212548818559 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨19, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41706211303581 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212548818559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13032_0 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (8407109562303 / 10000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106179592207 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨0, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (8407109562303 / 10000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106179592207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_1 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (16807241272403 / 20000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442472635811 / 20000000000000 : ℝ))
      (E := (cell13032 ⟨1, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (16807241272403 / 20000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442472635811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_2 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (84001341914347 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (88494686877 / 4000000000000 : ℝ))
      (E := (cell13032 ⟨2, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (84001341914347 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (88494686877 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_3 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (5247906390237 / 6250000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (11061855857 / 500000000000 : ℝ))
      (E := (cell13032 ⟨3, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (5247906390237 / 6250000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (11061855857 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_4 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (655716307143 / 781250000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212375185603 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨4, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (655716307143 / 781250000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212375185603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_5 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (8389689709003 / 10000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442475844479 / 20000000000000 : ℝ))
      (E := (cell13032 ⟨5, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (8389689709003 / 10000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442475844479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_6 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83862131535303 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553095807851 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨6, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83862131535303 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553095807851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_7 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83827390614643 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553096804979 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨7, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83827390614643 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553096804979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_8 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (20948168573189 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212391252993 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨8, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (20948168573189 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212391252993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_9 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83757982534531 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442479044277 / 20000000000000 : ℝ))
      (E := (cell13032 ⟨9, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83757982534531 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442479044277 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_10 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83723315305043 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442479849541 / 20000000000000 : ℝ))
      (E := (cell13032 ⟨10, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83723315305043 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442479849541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_11 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83688672569547 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212403222109 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨11, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83688672569547 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212403222109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_12 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83654054293477 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221240726681 / 10000000000000 : ℝ))
      (E := (cell13032 ⟨12, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83654054293477 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221240726681 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_13 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (1672389208849 / 2000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (138275704461 / 6250000000000 : ℝ))
      (E := (cell13032 ⟨13, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (1672389208849 / 2000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (138275704461 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_14 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83584890982261 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (44248305989 / 2000000000000 : ℝ))
      (E := (cell13032 ⟨14, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83584890982261 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (44248305989 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_15 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83550345878879 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106209649071 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨15, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83550345878879 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106209649071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_16 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (83515825098453 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106211636219 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨16, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (83515825098453 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106211636219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_17 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41740664303653 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553106821331 / 25000000000000 : ℝ))
      (E := (cell13032 ⟨17, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41740664303653 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (553106821331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_18 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41723428185967 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212431283109 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨18, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41723428185967 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212431283109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_19 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41706204179503 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106217664173 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨19, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41706204179503 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106217664173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13033_0 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (42035540628427 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442449132421 / 20000000000000 : ℝ))
      (E := (cell13033 ⟨0, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (42035540628427 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442449132421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_1 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (84036192002217 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212249651649 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨1, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (84036192002217 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212249651649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_2 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (84001327560921 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212253697359 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨2, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (84001327560921 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212253697359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_3 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (20991621974183 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (138266105741 / 6250000000000 : ℝ))
      (E := (cell13033 ⟨3, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (20991621974183 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (138266105741 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_4 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (20982918243401 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (276532712641 / 12500000000000 : ℝ))
      (E := (cell13033 ⟨4, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (20982918243401 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (276532712641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_5 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (16779376551137 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553066418769 / 25000000000000 : ℝ))
      (E := (cell13033 ⟨5, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (16779376551137 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553066418769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_6 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83862117207307 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (276533709903 / 12500000000000 : ℝ))
      (E := (cell13033 ⟨6, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83862117207307 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (276533709903 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_7 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83827376292991 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212273720927 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨7, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83827376292991 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212273720927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_8 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83792659977441 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (69133677851 / 3125000000000 : ℝ))
      (E := (cell13033 ⟨8, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83792659977441 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (69133677851 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_9 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83757968225549 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442456342591 / 20000000000000 : ℝ))
      (E := (cell13033 ⟨9, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83757968225549 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442456342591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_10 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83723301002387 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (17698285877 / 800000000000 : ℝ))
      (E := (cell13033 ⟨10, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83723301002387 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (17698285877 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_11 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (20922164568303 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (88491590501 / 4000000000000 : ℝ))
      (E := (cell13033 ⟨11, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (20922164568303 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (88491590501 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_12 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83654040003457 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (221229374457 / 10000000000000 : ℝ))
      (E := (cell13033 ⟨12, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83654040003457 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (221229374457 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_13 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (4180972307937 / 5000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106148872313 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨13, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (4180972307937 / 5000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106148872313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_14 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (16716975340971 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106150884119 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨14, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (16716975340971 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106150884119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_15 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (20887582901943 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212305762513 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨15, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (20887582901943 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212305762513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_16 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (2087895270841 / 2500000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442461958131 / 20000000000000 : ℝ))
      (E := (cell13033 ⟨16, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (2087895270841 / 2500000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442461958131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_17 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (4174065717439 / 5000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212313799241 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨17, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (4174065717439 / 5000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212313799241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_18 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (8344684211969 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106158896387 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨18, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (8344684211969 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106158896387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_19 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (83412394113039 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106160887759 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨19, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (83412394113039 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106160887759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13034_0 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (16814213378577 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553033048323 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨0, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (16814213378577 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553033048323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_1 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (672289421157 / 800000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212136177763 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨1, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (672289421157 / 800000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212136177763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_2 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (840013132097 / 1000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212140160559 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨2, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (840013132097 / 1000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212140160559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_3 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (20991618387969 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (69129506499 / 3125000000000 : ℝ))
      (E := (cell13034 ⟨3, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (20991618387969 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (69129506499 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_4 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (20982914658777 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212148212309 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨4, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (20982914658777 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212148212309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_5 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83896868423543 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553038045343 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨5, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83896868423543 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553038045343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_6 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83862102881513 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106078119333 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨6, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83862102881513 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106078119333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_7 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83827361973539 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212160217597 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨7, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83827361973539 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212160217597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_8 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (41896322832163 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553041060297 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨8, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (41896322832163 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553041060297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_9 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (16751590783753 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212168258239 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨9, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (16751590783753 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212168258239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_10 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83723286701929 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212172217207 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨10, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83723286701929 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212172217207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_11 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83688643979073 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (442435248101 / 20000000000000 : ℝ))
      (E := (cell13034 ⟨11, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83688643979073 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (442435248101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_12 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83654025715633 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212180276117 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨12, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83654025715633 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212180276117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_13 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (3344777275089 / 4000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212184271687 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨13, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (3344777275089 / 4000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212184271687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_14 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83584862429643 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (110609414543 / 5000000000000 : ℝ))
      (E := (cell13034 ⟨14, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83584862429643 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (110609414543 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_15 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (41775158669429 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212192280743 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨15, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (41775158669429 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212192280743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_16 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (41757898285509 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (110609815227 / 5000000000000 : ℝ))
      (E := (cell13034 ⟨16, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (41757898285509 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (110609815227 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_17 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (16696260018489 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212200308827 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨17, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (16696260018489 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212200308827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_18 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (20861706967409 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553051074527 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨18, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (20861706967409 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553051074527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_19 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (83412379869261 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212208334933 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨19, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (83412379869261 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212208334933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13035_0 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (84071052531123 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212018720133 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨0, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (84071052531123 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212018720133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_1 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (84036163289239 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106011349767 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨1, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (84036163289239 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106011349767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_2 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (21000324715171 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (442405347039 / 20000000000000 : ℝ))
      (E := (cell13035 ⟨2, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (21000324715171 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (442405347039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_3 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (10495807401153 / 12500000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106015359869 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨3, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (10495807401153 / 12500000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106015359869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_4 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (16786328859763 / 20000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553008679787 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨4, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (16786328859763 / 20000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553008679787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_5 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41948427046801 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212038741289 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨5, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41948427046801 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212038741289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_6 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83862088557919 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553010683947 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨6, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83862088557919 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553010683947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_7 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41913673828143 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (34563230749 / 1562500000000 : ℝ))
      (E := (cell13035 ⟨7, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41913673828143 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (34563230749 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_8 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (8379263135341 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (276506348351 / 12500000000000 : ℝ))
      (E := (cell13035 ⟨8, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (8379263135341 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (276506348351 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_9 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83757939614179 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106027370567 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨9, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83757939614179 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106027370567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_10 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83723272403667 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (221205875353 / 10000000000000 : ℝ))
      (E := (cell13035 ⟨10, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83723272403667 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (221205875353 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_11 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (8368862968713 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212062772249 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨11, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (8368862968713 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212062772249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_12 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (20913502857501 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (221206680333 / 10000000000000 : ℝ))
      (E := (cell13035 ⟨12, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (20913502857501 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (221206680333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_13 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (5226213599869 / 6250000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (442414158883 / 20000000000000 : ℝ))
      (E := (cell13035 ⟨13, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (5226213599869 / 6250000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (442414158883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_14 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (5224053009789 / 6250000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (44241496183 / 2000000000000 : ℝ))
      (E := (cell13035 ⟨14, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (5224053009789 / 6250000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (44241496183 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_15 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (10443787884017 / 12500000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212078794641 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨15, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (10443787884017 / 12500000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212078794641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_16 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83515782310587 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106041407047 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨16, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83515782310587 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106041407047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_17 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (834812858383 / 1000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212086814083 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨17, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (834812858383 / 1000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212086814083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_18 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83446813621771 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212090857377 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨18, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83446813621771 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212090857377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_19 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (83412365627671 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106047415867 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨19, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (83412365627671 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106047415867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13036_0 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (84071038171567 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211905242631 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨0, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (84071038171567 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211905242631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_1 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (42018074468029 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211909274827 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨1, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (42018074468029 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211909274827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_2 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (5250080282117 / 6250000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211913247599 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨2, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (5250080282117 / 6250000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211913247599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_3 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (3358657794751 / 4000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211917285079 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨3, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (3358657794751 / 4000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211917285079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_4 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (20982907491181 / 25000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211921279583 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨4, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (20982907491181 / 25000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211921279583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_5 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (83896839765863 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1105962648433 / 50000000000000 : ℝ))
      (E := (cell13036 ⟨5, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (83896839765863 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1105962648433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_6 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41931037118263 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211929286553 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨6, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41931037118263 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211929286553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_7 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41913666670617 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (138245832121 / 6250000000000 : ℝ))
      (E := (cell13036 ⟨7, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41913666670617 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (138245832121 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_8 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (20948154261173 / 25000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (221193732809 / 10000000000000 : ℝ))
      (E := (cell13036 ⟨8, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (20948154261173 / 25000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (221193732809 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_9 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (8375792531179 / 10000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211941335799 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨9, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (8375792531179 / 10000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211941335799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_10 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41861629053801 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211945343593 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨10, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41861629053801 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211945343593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_11 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (83688615397383 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211949357759 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨11, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (83688615397383 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211949357759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_12 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (83653997146569 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211953326209 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨12, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (83653997146569 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211953326209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_13 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (10452425415097 / 12500000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211957370957 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨13, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (10452425415097 / 12500000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211957370957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_14 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (83584833885797 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211961381279 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨14, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (83584833885797 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211961381279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_15 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (16710057761521 / 20000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211965362403 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨15, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (16710057761521 / 20000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211965362403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_16 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41757884026173 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (8640505381 / 390625000000 : ℝ))
      (E := (cell13036 ⟨16, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41757884026173 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (8640505381 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_17 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (10435158948293 / 12500000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211973373251 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨17, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (10435158948293 / 12500000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211973373251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_18 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (16689359875219 / 20000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211977412317 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨18, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (16689359875219 / 20000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2211977412317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_19 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (83412351388269 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1105990691247 / 50000000000000 : ℝ))
      (E := (cell13036 ⟨19, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (83412351388269 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1105990691247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13037_0 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (84071023814217 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552947954657 / 25000000000000 : ℝ))
      (E := (cell13037 ⟨0, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (84071023814217 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552947954657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_1 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (84036134585081 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (110589792289 / 5000000000000 : ℝ))
      (E := (cell13037 ⟨1, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (84036134585081 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (110589792289 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_2 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (5250079385579 / 6250000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105899935721 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨2, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (5250079385579 / 6250000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105899935721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_3 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83966430530529 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211803846081 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨3, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83966430530529 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211803846081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_4 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41965807816417 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211807893617 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨4, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41965807816417 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211807893617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_5 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (20974206360081 / 25000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (442362369621 / 20000000000000 : ℝ))
      (E := (cell13037 ⟨5, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (20974206360081 / 25000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (442362369621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_6 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83862059917333 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211815890963 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨6, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83862059917333 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211815890963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_7 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (4191365951419 / 5000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211819913607 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨7, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (4191365951419 / 5000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211819913607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_8 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (20948150684543 / 25000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211823923067 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨8, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (20948150684543 / 25000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211823923067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_9 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41878955505799 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211827926129 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨9, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41878955505799 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211827926129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_10 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83723243813733 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552957982331 / 25000000000000 : ℝ))
      (E := (cell13037 ⟨10, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83723243813733 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552957982331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_11 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83688601109831 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276479492367 / 12500000000000 : ℝ))
      (E := (cell13037 ⟨11, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83688601109831 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276479492367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_12 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83653982865329 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (13823999393 / 625000000000 : ℝ))
      (E := (cell13037 ⟨12, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83653982865329 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (13823999393 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_13 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83619389045841 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211843943169 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨13, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83619389045841 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211843943169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_14 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83584819617163 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211847949077 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨14, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83584819617163 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211847949077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_15 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (16710054909053 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552962981459 / 25000000000000 : ℝ))
      (E := (cell13037 ⟨15, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (16710054909053 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552962981459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_16 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (10439469224537 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211855936649 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨16, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (10439469224537 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211855936649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_17 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41740628668289 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552964996583 / 25000000000000 : ℝ))
      (E := (cell13037 ⟨17, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41740628668289 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552964996583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_18 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (83446785132607 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552965990733 / 25000000000000 : ℝ))
      (E := (cell13037 ⟨18, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (83446785132607 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (552965990733 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_19 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41706168575527 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (138241749201 / 6250000000000 : ℝ))
      (E := (cell13037 ⟨19, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41706168575527 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (138241749201 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13038_0 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (656804761399 / 781250000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211678448127 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨0, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (656804761399 / 781250000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211678448127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_1 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (84036120236309 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211682470257 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨1, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (84036120236309 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211682470257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_2 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (84001255826859 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105843216527 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨2, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (84001255826859 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105843216527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_3 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (16793283238897 / 20000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (138230653791 / 6250000000000 : ℝ))
      (E := (cell13038 ⟨3, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (16793283238897 / 20000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (138230653791 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_4 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41965800651573 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (17693555563 / 800000000000 : ℝ))
      (E := (cell13038 ⟨4, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41965800651573 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (17693555563 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_5 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41948405558493 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105849226483 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨5, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41948405558493 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105849226483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_6 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41931022800169 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211702491039 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨6, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41931022800169 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211702491039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_7 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (20956826179431 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105853254471 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨7, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (20956826179431 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105853254471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_8 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83792588433849 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (221171051371 / 10000000000000 : ℝ))
      (E := (cell13038 ⟨8, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83792588433849 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (221171051371 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_9 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83757896713603 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (17693716097 / 800000000000 : ℝ))
      (E := (cell13038 ⟨9, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83757896713603 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (17693716097 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_10 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83723229522059 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211718510721 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨10, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83723229522059 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211718510721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_11 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83688586824473 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105861257891 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨11, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83688586824473 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105861257891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_12 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83653968586281 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (69116454167 / 3125000000000 : ℝ))
      (E := (cell13038 ⟨12, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83653968586281 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (69116454167 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_13 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83619374773099 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (44234610221 / 2000000000000 : ℝ))
      (E := (cell13038 ⟨13, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83619374773099 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (44234610221 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_14 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (261202516721 / 312500000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211734570717 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨14, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (261202516721 / 312500000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211734570717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_15 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (20887565071279 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105869271567 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨15, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (20887565071279 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105869271567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_16 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (16703147908487 / 20000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552935637413 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨16, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (16703147908487 / 20000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552935637413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_17 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83481243089 / 100000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105873297543 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨17, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83481243089 / 100000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105873297543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_18 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (83446770891307 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552937641871 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨18, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (83446770891307 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552937641871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_19 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41706161458013 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211754587613 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨19, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41706161458013 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211754587613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13039_0 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (21017748776533 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (442313014657 / 20000000000000 : ℝ))
      (E := (cell13039 ⟨0, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (21017748776533 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (442313014657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_1 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (84036105889741 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105784545197 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨1, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (84036105889741 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105784545197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_2 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (1312519398229 / 1562500000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211573106109 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨2, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (1312519398229 / 1562500000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211573106109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_3 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83966401860643 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211577070893 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨3, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83966401860643 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211577070893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_4 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41965793487829 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221158110867 / 10000000000000 : ℝ))
      (E := (cell13039 ⟨4, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41965793487829 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221158110867 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_5 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83896796795847 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211585111451 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨5, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83896796795847 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211585111451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_6 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83862031285543 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105794543389 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨6, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83862031285543 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105794543389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_7 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83827290409267 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105796549971 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨7, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83827290409267 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105796549971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_8 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83792574131723 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211597100019 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨8, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83792574131723 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211597100019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_9 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83757882417803 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211601151843 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨9, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83757882417803 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211601151843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_10 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (4186160761629 / 5000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (276450643233 / 12500000000000 : ℝ))
      (E := (cell13039 ⟨10, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (4186160761629 / 5000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (276450643233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_11 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (8368857254131 / 10000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552902286599 / 25000000000000 : ℝ))
      (E := (cell13039 ⟨11, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (8368857254131 / 10000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552902286599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_12 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83653954309427 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211613159477 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨12, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83653954309427 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211613159477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_13 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83619360502549 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (138226074431 / 6250000000000 : ℝ))
      (E := (cell13039 ⟨13, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83619360502549 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (138226074431 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_14 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (20896197771617 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211621188029 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨14, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (20896197771617 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211621188029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_15 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83550246027157 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (442325031221 / 20000000000000 : ℝ))
      (E := (cell13039 ⟨15, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83550246027157 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (442325031221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_16 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (20878931322691 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (276453644791 / 12500000000000 : ℝ))
      (E := (cell13039 ⟨16, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (20878931322691 / 25000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (276453644791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_17 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (83481228843611 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (442326639903 / 20000000000000 : ℝ))
      (E := (cell13039 ⟨17, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (83481228843611 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (442326639903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_18 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41723378326097 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (276454653247 / 12500000000000 : ℝ))
      (E := (cell13039 ⟨18, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41723378326097 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (276454653247 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_19 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (5213269292699 / 6250000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105820620987 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨19, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (5213269292699 / 6250000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105820620987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13040_0 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (16814196151079 / 20000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211451694103 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨0, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (16814196151079 / 20000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211451694103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_1 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (2626127860793 / 3125000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211455706191 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨1, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (2626127860793 / 3125000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211455706191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_2 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (5250076696791 / 6250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105729858467 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨2, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (5250076696791 / 6250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105729858467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_3 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41983193764501 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105731867353 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨3, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41983193764501 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105731867353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_4 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83931572650371 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211467767627 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨4, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83931572650371 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211467767627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_5 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (20974195619227 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2764339707 / 125000000000 : ℝ))
      (E := (cell13040 ⟨5, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (20974195619227 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2764339707 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_6 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41931008486473 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105737868083 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨6, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41931008486473 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105737868083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_7 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41913638051503 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (276434968077 / 12500000000000 : ℝ))
      (E := (cell13040 ⟨7, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41913638051503 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (276434968077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_8 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41896279915897 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (442296759611 / 20000000000000 : ℝ))
      (E := (cell13040 ⟨8, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41896279915897 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (442296759611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_9 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83757868124199 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552871946807 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨9, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83757868124199 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552871946807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_10 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (5232700059081 / 6250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (88459671067 / 4000000000000 : ℝ))
      (E := (cell13040 ⟨10, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (5232700059081 / 6250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (88459671067 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_11 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83688558260339 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211495772681 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨11, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83688558260339 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211495772681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_12 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (16730788006953 / 20000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211499781281 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨12, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (16730788006953 / 20000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211499781281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_13 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (8361934623419 / 10000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211503808267 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨13, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (8361934623419 / 10000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211503808267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_14 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83584776824407 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552876950253 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨14, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83584776824407 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552876950253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_15 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (20887557942847 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105755911471 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨15, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (20887557942847 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105755911471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_16 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83515711041281 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (69109869403 / 3125000000000 : ℝ))
      (E := (cell13040 ⟨16, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83515711041281 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (69109869403 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_17 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (83481214600409 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211519857859 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨17, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (83481214600409 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211519857859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_18 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (20861685603817 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211523880143 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨18, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (20861685603817 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211523880143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_19 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (5213268403283 / 6250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211527833723 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨19, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (5213268403283 / 6250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211527833723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13041_0 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (84070966406863 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (88453534737 / 4000000000000 : ℝ))
      (E := (cell13041 ⟨0, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (84070966406863 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (88453534737 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_1 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (84036077203213 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211342375519 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨1, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (84036077203213 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211342375519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_2 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (42000606406429 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (4319035901 / 195312500000 : ℝ))
      (E := (cell13041 ⟨2, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (42000606406429 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (4319035901 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_3 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41983186599781 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211350394183 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨3, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41983186599781 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211350394183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_4 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (20982889581821 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211354422249 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨4, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (20982889581821 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211354422249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_5 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (10487096020021 / 12500000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442271683083 / 20000000000000 : ℝ))
      (E := (cell13041 ⟨5, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (10487096020021 / 12500000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442271683083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_6 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83862002662547 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552840609801 / 25000000000000 : ℝ))
      (E := (cell13041 ⟨6, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83862002662547 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552840609801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_7 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83827261798943 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552841610741 / 25000000000000 : ℝ))
      (E := (cell13041 ⟨7, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83827261798943 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552841610741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_8 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (4189627276703 / 5000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (221137043373 / 10000000000000 : ℝ))
      (E := (cell13041 ⟨8, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (4189627276703 / 5000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (221137043373 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_9 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (8375785383279 / 10000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211374418283 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨9, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (8375785383279 / 10000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211374418283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_10 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (16744637332041 / 20000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105689230617 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨10, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (16744637332041 / 20000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105689230617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_11 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41844271990781 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211382452737 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨11, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41844271990781 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211382452737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_12 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (16730785152459 / 20000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105693228441 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨12, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (16730785152459 / 20000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105693228441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_13 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41809665984011 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105695239729 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨13, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41809665984011 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105695239729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_14 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (10448095320567 / 12500000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211394467841 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨14, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (10448095320567 / 12500000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211394467841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_15 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (5221888594863 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442279697091 / 20000000000000 : ℝ))
      (E := (cell13041 ⟨15, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (5221888594863 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442279697091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_16 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41757848396993 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (110570123957 / 5000000000000 : ℝ))
      (E := (cell13041 ⟨16, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41757848396993 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (110570123957 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_17 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41740600179697 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211406511881 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨17, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41740600179697 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211406511881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_18 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (5215420511283 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552852632497 / 25000000000000 : ℝ))
      (E := (cell13041 ⟨18, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (5215420511283 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552852632497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_19 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (83412280224057 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211414537727 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨19, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (83412280224057 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211414537727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13042_0 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (42035476030267 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105612548127 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨0, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (42035476030267 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105612548127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_1 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (21009015715813 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211229098377 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨1, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (21009015715813 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211229098377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_2 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (4200059923963 / 5000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105616549623 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨2, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (4200059923963 / 5000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105616549623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_3 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83966358872323 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105618553619 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨3, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83966358872323 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105618553619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_4 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (20982886001599 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105620536269 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨4, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (20982886001599 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105620536269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_5 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (134234806153 / 160000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211245118859 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨5, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (134234806153 / 160000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211245118859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_6 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (16772397670869 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211249137911 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨6, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (16772397670869 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211249137911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_7 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (3353089899883 / 4000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105626568491 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨7, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (3353089899883 / 4000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105626568491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_8 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41896265619261 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (69101785097 / 3125000000000 : ℝ))
      (E := (cell13042 ⟨8, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41896265619261 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (69101785097 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_9 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (3350313581743 / 4000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552815290279 / 25000000000000 : ℝ))
      (E := (cell13042 ⟨9, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (3350313581743 / 4000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552815290279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_10 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (20930793094327 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442253028293 / 20000000000000 : ℝ))
      (E := (cell13042 ⟨10, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (20930793094327 / 25000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442253028293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_11 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83688529704977 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442253825693 / 20000000000000 : ℝ))
      (E := (cell13042 ⟨11, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83688529704977 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442253825693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_12 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83653911492017 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211273186279 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨12, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83653911492017 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211273186279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_13 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (16723863540809 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211277146323 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨13, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (16723863540809 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211277146323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_14 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41792374153427 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442256237703 / 20000000000000 : ℝ))
      (E := (cell13042 ⟨14, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41792374153427 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442256237703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_15 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (5221887704151 / 6250000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105642600919 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨15, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (5221887704151 / 6250000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105642600919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_16 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83515682548879 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211289191277 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨16, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83515682548879 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211289191277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_17 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41740593060283 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (110564660991 / 5000000000000 : ℝ))
      (E := (cell13042 ⟨17, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41740593060283 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (110564660991 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_18 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (83446713947973 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211297233777 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨18, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (83446713947973 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211297233777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_19 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (8341226599777 / 10000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211301237411 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨19, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (8341226599777 / 10000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211301237411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13043_0 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (84070937716407 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105555880951 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨0, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (84070937716407 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105555880951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_1 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (42018024262747 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211115816897 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨1, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (42018024262747 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211115816897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_2 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (10500148018483 / 12500000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211119812843 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨2, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (10500148018483 / 12500000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211119812843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_3 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41983172273641 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211123815961 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨3, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41983172273641 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211123815961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_4 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41965764843853 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (8637218103 / 390625000000 : ℝ))
      (E := (cell13043 ⟨4, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41965764843853 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (8637218103 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_5 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83896739533281 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (138195738623 / 6250000000000 : ℝ))
      (E := (cell13043 ⟨5, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83896739533281 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (138195738623 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_6 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (4193098702417 / 5000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (442227166457 / 20000000000000 : ℝ))
      (E := (cell13043 ⟨6, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (4193098702417 / 5000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (442227166457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_7 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20956808299351 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211139826667 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨7, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20956808299351 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211139826667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_8 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41896258472589 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (110557193309 / 5000000000000 : ℝ))
      (E := (cell13043 ⟨8, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41896258472589 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (110557193309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_9 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41878912628277 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105573920783 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨9, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41878912628277 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105573920783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_10 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20930789524151 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552787968861 / 25000000000000 : ℝ))
      (E := (cell13043 ⟨10, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20930789524151 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552787968861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_11 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (10461064428823 / 12500000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211155857967 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨11, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (10461064428823 / 12500000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211155857967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_12 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (8365389722393 / 10000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105579926613 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨12, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (8365389722393 / 10000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105579926613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_13 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83619303442257 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211163867011 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨13, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83619303442257 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211163867011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_14 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83584734051361 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (442233580973 / 20000000000000 : ℝ))
      (E := (cell13043 ⟨14, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83584734051361 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (442233580973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_15 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20887547254303 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211171913897 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨15, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20887547254303 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211171913897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_16 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (83515668305959 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211175899093 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨16, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (83515668305959 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211175899093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_17 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20870292970981 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105589961719 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨17, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20870292970981 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105589961719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_18 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20861674929401 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552795983311 / 25000000000000 : ℝ))
      (E := (cell13043 ⟨18, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20861674929401 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552795983311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_19 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20853062943417 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105593966387 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨19, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20853062943417 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105593966387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13044_0 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (42035461687241 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105499269451 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨0, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (42035461687241 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105499269451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_1 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (5252252136871 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552750632771 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨1, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (5252252136871 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552750632771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_2 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (84001169818667 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552751630527 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨2, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (84001169818667 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552751630527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_3 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83966330224441 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (44220210407 / 2000000000000 : ℝ))
      (E := (cell13044 ⟨3, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83966330224441 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (44220210407 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_4 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (16786303074243 / 20000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276376816741 / 12500000000000 : ℝ))
      (E := (cell13044 ⟨4, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (16786303074243 / 20000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276376816741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_5 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41948362611567 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211018570707 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨5, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41948362611567 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211018570707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_6 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83861959744531 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105511290157 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨6, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83861959744531 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105511290157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_7 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (10478402362491 / 12500000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (138189160627 / 6250000000000 : ℝ))
      (E := (cell13044 ⟨7, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (10478402362491 / 12500000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (138189160627 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_8 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83792502654029 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211030604927 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨8, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83792502654029 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211030604927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_9 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41878905485863 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211034575743 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨9, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41878905485863 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211034575743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_10 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (20930785954523 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211038605097 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨10, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (20930785954523 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211038605097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_11 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41844250579191 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276380322893 / 12500000000000 : ℝ))
      (E := (cell13044 ⟨11, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41844250579191 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276380322893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_12 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83653882958033 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (69095207253 / 3125000000000 : ℝ))
      (E := (cell13044 ⟨12, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83653882958033 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (69095207253 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_13 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (4180964459133 / 5000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211050641521 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨13, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (4180964459133 / 5000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211050641521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_14 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83584719798057 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552763654223 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨14, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83584719798057 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552763654223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_15 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (20887543692549 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105529310817 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨15, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (20887543692549 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105529310817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_16 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (3340626162609 / 4000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442212532161 / 20000000000000 : ℝ))
      (E := (cell13044 ⟨16, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (3340626162609 / 4000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442212532161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_17 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83481157649467 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105533340489 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨17, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83481157649467 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105533340489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_18 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (83446685489419 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211070686657 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨18, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (83446685489419 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211070686657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_19 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (333648950207 / 400000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211074682107 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨19, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (333648950207 / 400000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211074682107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13045_0 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (84070909034759 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210885253723 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨0, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (84070909034759 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210885253723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_1 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (84036019856579 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552722324701 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨1, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (84036019856579 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552722324701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_2 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (8400115549167 / 10000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (221089328493 / 10000000000000 : ℝ))
      (E := (cell13045 ⟨2, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (8400115549167 / 10000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (221089328493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_3 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83966315903799 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (27636215979 / 1250000000000 : ℝ))
      (E := (cell13045 ⟨3, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83966315903799 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (27636215979 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_4 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83931501056921 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (442180257419 / 20000000000000 : ℝ))
      (E := (cell13045 ⟨4, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83931501056921 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (442180257419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_5 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83896710915183 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210905319117 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨5, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83896710915183 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210905319117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_6 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41930972721459 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210909324013 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨6, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41930972721459 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210909324013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_7 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41913602302323 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552728327267 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨7, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41913602302323 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552728327267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_8 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41896244182537 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105458669673 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨8, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41896244182537 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105458669673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_9 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20939449172273 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105460681823 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨9, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20939449172273 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105460681823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_10 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20930782385443 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (88437013217 / 4000000000000 : ℝ))
      (E := (cell13045 ⟨10, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20930782385443 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (88437013217 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_11 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20922121722093 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (138183085131 / 6250000000000 : ℝ))
      (E := (cell13045 ⟨11, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20922121722093 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (138183085131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_12 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41826934347163 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210933348519 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨12, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41826934347163 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210933348519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_13 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83619274925251 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210937353561 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨13, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83619274925251 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210937353561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_14 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83584705546941 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210941382767 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨14, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83584705546941 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210941382767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_15 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (83550160525367 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552736345811 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨15, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (83550160525367 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552736345811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_16 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41757819913339 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552737354549 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨16, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41757819913339 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552737354549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_17 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20870285854299 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210953434197 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨17, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20870285854299 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210953434197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_18 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41723335631709 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210957435751 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨18, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41723335631709 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2210957435751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_19 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41706111666007 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105480713561 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨19, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41706111666007 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105480713561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13046_0 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (84070894697237 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210772079899 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨0, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (84070894697237 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210772079899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_1 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (42018002762711 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210776062191 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨1, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (42018002762711 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210776062191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_2 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (84001141166873 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221078010131 / 10000000000000 : ℝ))
      (E := (cell13046 ⟨2, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (84001141166873 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221078010131 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_3 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (16793260317071 / 20000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210784089873 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨3, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (16793260317071 / 20000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210784089873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_4 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (3357259469793 / 4000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210788093869 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨4, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (3357259469793 / 4000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210788093869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_5 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83896696609429 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105396060579 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨5, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83896696609429 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105396060579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_6 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (167723862287 / 200000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (276349515171 / 12500000000000 : ℝ))
      (E := (cell13046 ⟨6, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (167723862287 / 200000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (276349515171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_7 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83827190311559 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (276350012723 / 12500000000000 : ℝ))
      (E := (cell13046 ⟨7, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83827190311559 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (276350012723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_8 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (10474059259789 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221080412747 / 10000000000000 : ℝ))
      (E := (cell13046 ⟨8, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (10474059259789 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221080412747 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_9 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83757782408649 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105404073613 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨9, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83757782408649 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105404073613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_10 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (20930778816911 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105406083791 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨10, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (20930778816911 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105406083791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_11 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83688472620551 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (88432645469 / 4000000000000 : ℝ))
      (E := (cell13046 ⟨11, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83688472620551 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (88432645469 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_12 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (10456731804101 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (552705044217 / 25000000000000 : ℝ))
      (E := (cell13046 ⟨12, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (10456731804101 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (552705044217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_13 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (8361926067003 / 10000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (276353022197 / 12500000000000 : ℝ))
      (E := (cell13046 ⟨13, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (8361926067003 / 10000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (276353022197 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_14 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (20896172824503 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210828144323 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨14, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (20896172824503 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210828144323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_15 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (20887536570681 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221083219873 / 10000000000000 : ℝ))
      (E := (cell13046 ⟨15, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (20887536570681 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221083219873 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_16 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (20878906397579 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210836171269 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨16, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (20878906397579 / 25000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210836171269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_17 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83481129187109 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210840183099 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨17, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83481129187109 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210840183099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_18 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (83446657039601 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (138177761283 / 6250000000000 : ℝ))
      (E := (cell13046 ⟨18, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (83446657039601 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (138177761283 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_19 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (41706104557231 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210848226109 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨19, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (41706104557231 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210848226109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13047_0 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (21017720090479 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105329421949 / 50000000000000 : ℝ))
      (E := (cell13047 ⟨0, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (21017720090479 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105329421949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_1 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (16807198239293 / 20000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105331439557 / 50000000000000 : ℝ))
      (E := (cell13047 ⟨1, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (16807198239293 / 20000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105331439557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_2 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (42000563422137 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210666855469 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨2, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (42000563422137 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210666855469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_3 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83966287269109 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210670897097 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨3, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83966287269109 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210670897097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_4 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41965736217463 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210674896313 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨4, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41965736217463 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210674896313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_5 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83896682305871 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210678918871 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨5, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83896682305871 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210678918871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_6 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83861916846277 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (552670728599 / 25000000000000 : ℝ))
      (E := (cell13047 ⟨6, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83861916846277 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (552670728599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_7 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41913588010333 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105343445087 / 50000000000000 : ℝ))
      (E := (cell13047 ⟨7, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41913588010333 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105343445087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_8 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83792459793743 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210690911269 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨8, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83792459793743 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210690911269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_9 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41878884065199 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (27633686581 / 1250000000000 : ℝ))
      (E := (cell13047 ⟨9, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41878884065199 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (27633686581 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_10 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41861550497853 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (110534947117 / 5000000000000 : ℝ))
      (E := (cell13047 ⟨10, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41861550497853 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (110534947117 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_11 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83688458354921 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (552675741283 / 25000000000000 : ℝ))
      (E := (cell13047 ⟨11, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83688458354921 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (552675741283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_12 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (2091346004337 / 2500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (221070694277 / 10000000000000 : ℝ))
      (E := (cell13047 ⟨12, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (2091346004337 / 2500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (221070694277 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_13 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41809623208499 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (552677749317 / 25000000000000 : ℝ))
      (E := (cell13047 ⟨13, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41809623208499 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (552677749317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_14 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (8358467705127 / 10000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210714959729 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨14, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (8358467705127 / 10000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210714959729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_15 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (20887533010567 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (442143801979 / 20000000000000 : ℝ))
      (E := (cell13047 ⟨15, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (20887533010567 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (442143801979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_16 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83515611356139 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210722978241 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨16, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83515611356139 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210722978241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_17 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83481114959207 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210726985923 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨17, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83481114959207 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210726985923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_18 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (5215415176123 / 6250000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210731037517 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨18, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (5215415176123 / 6250000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210731037517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_19 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (83412194899091 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (110536751039 / 5000000000000 : ℝ))
      (E := (cell13047 ⟨19, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (83412194899091 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (110536751039 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13048_0 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (16814173205759 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105272859627 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨0, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (16814173205759 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105272859627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_1 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (84035976869707 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210549691707 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨1, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (84035976869707 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210549691707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_2 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (84001112523873 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210553721081 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨2, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (84001112523873 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210553721081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_3 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83966272955059 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210557699993 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨3, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83966272955059 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210557699993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_4 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (41965729063611 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210561694431 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨4, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (41965729063611 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210561694431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_5 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83896668004507 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105282856129 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨5, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83896668004507 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105282856129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_6 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (5241368909453 / 6250000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210569761083 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨6, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (5241368909453 / 6250000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210569761083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_7 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (41913580865983 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210573732247 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨7, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (41913580865983 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210573732247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_8 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (41896222755683 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (88423109951 / 4000000000000 : ℝ))
      (E := (cell13048 ⟨8, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (41896222755683 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (88423109951 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_9 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83757753854339 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105290879733 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨9, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83757753854339 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105290879733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_10 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83723086725959 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552646442713 / 25000000000000 : ℝ))
      (E := (cell13048 ⟨10, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83723086725959 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552646442713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_11 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (2092211102287 / 2500000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105294894609 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨11, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (2092211102287 / 2500000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105294894609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_12 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83653825916339 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210593762477 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨12, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83653825916339 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210593762477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_13 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83619232166153 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105298906321 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨13, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83619232166153 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105298906321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_14 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (16716932561343 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210601828987 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨14, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (16716932561343 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210601828987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_15 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83550117803997 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210605816743 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨15, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83550117803997 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210605816743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_16 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83515597124147 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105304919557 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨16, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83515597124147 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105304919557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_17 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (5217568795843 / 6250000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105306921337 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨17, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (5217568795843 / 6250000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105306921337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_18 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83446628598517 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210617831927 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨18, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83446628598517 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210617831927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_19 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (83412180685903 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (88424874777 / 4000000000000 : ℝ))
      (E := (cell13048 ⟨19, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (83412180685903 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (88424874777 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13049_0 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (84070851697873 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (442086506487 / 20000000000000 : ℝ))
      (E := (cell13049 ⟨0, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (84070851697873 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (442086506487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_1 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (84035962545147 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210436557837 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨1, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (84035962545147 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210436557837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_2 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (8400109820567 / 10000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105220291181 / 50000000000000 : ℝ))
      (E := (cell13049 ⟨2, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (8400109820567 / 10000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105220291181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_3 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83966258643207 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105222278237 / 50000000000000 : ℝ))
      (E := (cell13049 ⟨3, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83966258643207 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105222278237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_4 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41965721910857 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210448546159 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨4, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41965721910857 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210448546159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_5 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83896653705339 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105226279639 / 50000000000000 : ℝ))
      (E := (cell13049 ⟨5, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83896653705339 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105226279639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_6 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83861888258413 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552614150861 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨6, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83861888258413 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552614150861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_7 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83827147445459 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105230284997 / 50000000000000 : ℝ))
      (E := (cell13049 ⟨7, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83827147445459 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105230284997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_8 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83792431231181 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552616145489 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨8, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83792431231181 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552616145489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_9 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83757739580471 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (69077143379 / 3125000000000 : ℝ))
      (E := (cell13049 ⟨9, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83757739580471 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (69077143379 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_10 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83723072458401 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105236297521 / 50000000000000 : ℝ))
      (E := (cell13049 ⟨10, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83723072458401 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105236297521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_11 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (20922107457557 / 25000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210476608983 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨11, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (20922107457557 / 25000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210476608983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_12 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83653811661387 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210480635987 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨12, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83653811661387 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210480635987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_13 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (16723843583499 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (138155288981 / 6250000000000 : ℝ))
      (E := (cell13049 ⟨13, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (16723843583499 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (138155288981 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_14 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41792324282173 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552622158939 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨14, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41792324282173 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552622158939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_15 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83550103567911 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552623169367 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨15, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83550103567911 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552623169367 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_16 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (83515582894339 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210496695671 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨16, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (83515582894339 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210496695671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_17 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (652195988359 / 781250000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210500695109 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨17, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (652195988359 / 781250000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210500695109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_18 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (1303853349707 / 1562500000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210504680287 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨18, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (1303853349707 / 1562500000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210504680287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_19 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (16682433294979 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210508713757 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨19, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (16682433294979 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210508713757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

end BstLean.Part268
