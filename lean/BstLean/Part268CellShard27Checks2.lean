import BstLean.Part268CellShard27Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13025_40 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (4134731854629 / 5000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106657363777 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨40, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (4134731854629 / 5000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106657363777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_41 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (16532142766837 / 20000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213318750623 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨41, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (16532142766837 / 20000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213318750623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_42 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (82626814076983 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (88532909501 / 4000000000000 : ℝ))
      (E := (cell13025 ⟨42, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (82626814076983 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (88532909501 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_43 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (16518587558297 / 20000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213326745833 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨43, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (16518587558297 / 20000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213326745833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_44 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (1651181698967 / 2000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (17706646193 / 800000000000 : ℝ))
      (E := (cell13025 ⟨44, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (1651181698967 / 2000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (17706646193 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_45 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (82525255518387 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (442666952373 / 20000000000000 : ℝ))
      (E := (cell13025 ⟨45, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (82525255518387 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (442666952373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_46 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (82491449472549 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (44266775321 / 2000000000000 : ℝ))
      (E := (cell13025 ⟨46, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (82491449472549 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (44266775321 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_47 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (5153604173871 / 6250000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213342784609 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨47, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (5153604173871 / 6250000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213342784609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_48 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (1287873553403 / 1562500000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106673407631 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨48, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (1287873553403 / 1562500000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106673407631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_49 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41195085675753 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (88534031861 / 4000000000000 : ℝ))
      (E := (cell13025 ⟨49, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41195085675753 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (88534031861 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_50 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (82356458554609 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213354843647 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨50, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (82356458554609 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213354843647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_51 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (10290346124847 / 12500000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213358835707 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨51, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (10290346124847 / 12500000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213358835707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_52 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41144551327911 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106681443813 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨52, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41144551327911 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106681443813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_53 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (82255459497703 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (553341719493 / 25000000000000 : ℝ))
      (E := (cell13025 ⟨53, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (82255459497703 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (553341719493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_54 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (16444367899303 / 20000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106685431117 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨54, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (16444367899303 / 20000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106685431117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_55 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41094121312247 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106687447893 / 50000000000000 : ℝ))
      (E := (cell13025 ⟨55, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41094121312247 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (1106687447893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_56 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (82154668854013 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (8646011389 / 390625000000 : ℝ))
      (E := (cell13025 ⟨56, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (82154668854013 / 100000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (8646011389 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_57 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (41060559078791 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213382917459 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨57, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (41060559078791 / 50000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213382917459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_58 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (1641751810157 / 2000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213386956237 / 100000000000000 : ℝ))
      (E := (cell13025 ⟨58, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (1641751810157 / 2000000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (2213386956237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13025_59 : CellCertificate 13025 (219457150075639 / 2500000000000000 : ℝ) (100788178422689 / 62500000000000000 : ℝ) (325546850289417 / 10000000000000000 : ℝ)
    (cell13025 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · norm_num [cell13025]
  · have h := gap_lower (n := 13025) (a := (102567607347 / 125000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (442678193637 / 20000000000000 : ℝ))
      (E := (cell13025 ⟨59, by decide⟩).energy) (xi := (325546850289417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13025 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13025]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13025])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13025) (a := (102567607347 / 125000000000 : ℝ)) (b := (6323796331 / 4000000000000 : ℝ)) (q := (442678193637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13025])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13025]

theorem cert13026_40 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41347311481003 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213201068049 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨40, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41347311481003 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213201068049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_41 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (4133034985489 / 5000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213205087877 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨41, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (4133034985489 / 5000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213205087877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_42 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82626799958741 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442641814317 / 20000000000000 : ℝ))
      (E := (cell13026 ⟨42, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82626799958741 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442641814317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_43 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82592923679401 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106606538373 / 50000000000000 : ℝ))
      (E := (cell13026 ⟨43, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82592923679401 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106606538373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_44 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82559070842419 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (138326068871 / 6250000000000 : ℝ))
      (E := (cell13026 ⟨44, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82559070842419 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (138326068871 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_45 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (20631310354651 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213221086621 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨45, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (20631310354651 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213221086621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_46 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82491435378909 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442645029343 / 20000000000000 : ℝ))
      (E := (cell13026 ⟨46, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82491435378909 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442645029343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_47 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41228826347217 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442645832467 / 20000000000000 : ℝ))
      (E := (cell13026 ⟨47, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41228826347217 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442645832467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_48 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82423893336423 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213233131129 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨48, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82423893336423 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213233131129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_49 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41195078638133 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213237168509 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨49, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41195078638133 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213237168509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_50 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (20589111121373 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276655144227 / 12500000000000 : ℝ))
      (E := (cell13026 ⟨50, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (20589111121373 / 25000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (276655144227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_51 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41161377467889 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (553311300533 / 25000000000000 : ℝ))
      (E := (cell13026 ⟨51, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41161377467889 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (553311300533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_52 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82289088598937 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213249192283 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨52, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82289088598937 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213249192283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_53 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82255445446927 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (110662658997 / 5000000000000 : ℝ))
      (E := (cell13026 ⟨53, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82255445446927 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (110662658997 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_54 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82221825451843 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213257220667 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨54, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82221825451843 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213257220667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_55 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82188228585921 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106630625823 / 50000000000000 : ℝ))
      (E := (cell13026 ⟨55, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82188228585921 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (1106630625823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_56 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (82154654821533 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213265268919 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨56, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (82154654821533 / 100000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213265268919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_57 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (10265138016399 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213269268313 / 100000000000000 : ℝ))
      (E := (cell13026 ⟨57, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (10265138016399 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (2213269268313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_58 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (10260947060943 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (138329577841 / 6250000000000 : ℝ))
      (E := (cell13026 ⟨58, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (10260947060943 / 12500000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (138329577841 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13026_59 : CellCertificate 13026 (877801987147269 / 10000000000000000 : ℝ) (806243507843657 / 500000000000000000 : ℝ) (325521278351003 / 10000000000000000 : ℝ)
    (cell13026 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · norm_num [cell13026]
  · have h := gap_lower (n := 13026) (a := (41027035931687 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442655462843 / 20000000000000 : ℝ))
      (E := (cell13026 ⟨59, by decide⟩).energy) (xi := (325521278351003 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13026 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13026]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13026])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13026) (a := (41027035931687 / 50000000000000 : ℝ)) (b := (39520657651 / 25000000000000 : ℝ)) (q := (442655462843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13026])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13026]

theorem cert13027_40 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (16538921766721 / 20000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (88523496169 / 4000000000000 : ℝ))
      (E := (cell13027 ⟨40, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (16538921766721 / 20000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (88523496169 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_41 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41330342793773 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106545710407 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨41, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41330342793773 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106545710407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_42 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82626785842669 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (221309540133 / 10000000000000 : ℝ))
      (E := (cell13027 ⟨42, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82626785842669 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (221309540133 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_43 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41296454784743 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (138318716387 / 6250000000000 : ℝ))
      (E := (cell13027 ⟨43, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41296454784743 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (138318716387 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_44 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82559056738657 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213103425433 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨44, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82559056738657 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213103425433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_45 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82525227320989 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213107465959 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨45, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82525227320989 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213107465959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_46 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (20622855321859 / 25000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213111464149 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨46, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (20622855321859 / 25000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213111464149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_47 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41228819304549 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106557738403 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨47, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41228819304549 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106557738403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_48 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (4121193962861 / 5000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (138319968853 / 6250000000000 : ℝ))
      (E := (cell13027 ⟨48, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (4121193962861 / 5000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (138319968853 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_49 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82390143203189 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213123536183 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨49, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82390143203189 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213123536183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_50 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41178215209269 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (69160234959 / 3125000000000 : ℝ))
      (E := (cell13027 ⟨50, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41178215209269 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (69160234959 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_51 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82322740874941 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (8852526257 / 400000000000 : ℝ))
      (E := (cell13027 ⟨51, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82322740874941 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (8852526257 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_52 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82289074544213 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213135551691 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨52, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82289074544213 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213135551691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_53 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (8225543139831 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106569768343 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨53, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (8225543139831 / 10000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106569768343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_54 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82221811409329 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442628714959 / 20000000000000 : ℝ))
      (E := (cell13027 ⟨54, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82221811409329 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442628714959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_55 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (16437642909901 / 20000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213147603203 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨55, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (16437642909901 / 20000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213147603203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_56 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (82154640791211 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213151617949 / 100000000000000 : ℝ))
      (E := (cell13027 ⟨56, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (82154640791211 / 100000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (2213151617949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_57 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41060545053479 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (138322225929 / 6250000000000 : ℝ))
      (E := (cell13027 ⟨57, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41060545053479 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (138322225929 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_58 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41043781234697 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106579824387 / 50000000000000 : ℝ))
      (E := (cell13027 ⟨58, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41043781234697 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (1106579824387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13027_59 : CellCertificate 13027 (219443844476319 / 2500000000000000 : ℝ) (12898905565043 / 8000000000000000 : ℝ) (162747855231467 / 5000000000000000 : ℝ)
    (cell13027 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · norm_num [cell13027]
  · have h := gap_lower (n := 13027) (a := (41027028925651 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442632731189 / 20000000000000 : ℝ))
      (E := (cell13027 ⟨59, by decide⟩).energy) (xi := (162747855231467 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13027 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13027]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13027])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13027) (a := (41027028925651 / 50000000000000 : ℝ)) (b := (4939698589 / 3125000000000 : ℝ)) (q := (442632731189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13027])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13027]

theorem cert13028_40 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (5168412169211 / 6250000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212973794861 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨40, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (5168412169211 / 6250000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212973794861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_41 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82660671467483 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553244452059 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨41, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82660671467483 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553244452059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_42 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82626771728767 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (138311361599 / 6250000000000 : ℝ))
      (E := (cell13028 ⟨42, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82626771728767 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (138311361599 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_43 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (4129644773087 / 5000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553246460831 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨43, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (4129644773087 / 5000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553246460831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_44 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41279521318531 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (69155931359 / 3125000000000 : ℝ))
      (E := (cell13028 ⟨44, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41279521318531 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (69155931359 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_45 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (4126260661277 / 5000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276624230123 / 12500000000000 : ℝ))
      (E := (cell13028 ⟨45, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (4126260661277 / 5000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276624230123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_46 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82491407198129 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212997836189 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨46, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82491407198129 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2212997836189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_47 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82457624525927 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553250461477 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨47, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82457624525927 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553250461477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_48 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (4121193259009 / 5000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213005867859 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨48, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (4121193259009 / 5000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213005867859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_49 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (20597532283069 / 25000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106504949773 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨49, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (20597532283069 / 25000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106504949773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_50 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41178208176873 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553253469813 / 25000000000000 : ℝ))
      (E := (cell13028 ⟨50, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41178208176873 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (553253469813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_51 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41161363408133 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213017922059 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨51, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41161363408133 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213017922059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_52 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82289060491649 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276627738349 / 12500000000000 : ℝ))
      (E := (cell13028 ⟨52, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82289060491649 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (276627738349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_53 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41127708675927 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213025948207 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨53, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41127708675927 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213025948207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_54 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41110898684487 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213029924617 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨54, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41110898684487 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213029924617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_55 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82188200515247 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (442606790091 / 20000000000000 : ℝ))
      (E := (cell13028 ⟨55, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82188200515247 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (442606790091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_56 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (16430925352609 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213037962677 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨56, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (16430925352609 / 20000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213037962677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_57 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (82121076084879 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (221304201629 / 10000000000000 : ℝ))
      (E := (cell13028 ⟨57, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (82121076084879 / 100000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (221304201629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_58 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (41043774226699 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213045988589 / 100000000000000 : ℝ))
      (E := (cell13028 ⟨58, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (41043774226699 / 50000000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (2213045988589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13028_59 : CellCertificate 13028 (109718596571959 / 1250000000000000 : ℝ) (64489575783513 / 40000000000000000 : ℝ) (325470146624187 / 10000000000000000 : ℝ)
    (cell13028 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · norm_num [cell13028]
  · have h := gap_lower (n := 13028) (a := (10256755480173 / 12500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106524996687 / 50000000000000 : ℝ))
      (E := (cell13028 ⟨59, by decide⟩).energy) (xi := (325470146624187 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13028 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13028]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13028])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13028) (a := (10256755480173 / 12500000000000 : ℝ)) (b := (158058081007 / 100000000000000 : ℝ)) (q := (1106524996687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13028])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13028]

theorem cert13029_40 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82694580583317 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212860181183 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨40, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82694580583317 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212860181183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_41 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (8266065734959 / 10000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (138304011959 / 6250000000000 : ℝ))
      (E := (cell13029 ⟨41, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (8266065734959 / 10000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (138304011959 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_42 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (16525351523407 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553217056087 / 25000000000000 : ℝ))
      (E := (cell13029 ⟨42, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (16525351523407 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (553217056087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_43 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82592881356163 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106436110071 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨43, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82592881356163 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106436110071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_44 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (16511805707527 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212876236103 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨44, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (16511805707527 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212876236103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_45 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41262599566129 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212880270593 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨45, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41262599566129 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212880270593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_46 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82491393110987 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212884262839 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨46, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82491393110987 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212884262839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_47 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82457610444921 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212888269643 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨47, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82457610444921 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212888269643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_48 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (10302981388163 / 12500000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106446144363 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨48, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (10302981388163 / 12500000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106446144363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_49 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (3295604602541 / 4000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (276612039699 / 12500000000000 : ℝ))
      (E := (cell13029 ⟨49, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (3295604602541 / 4000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (276612039699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_50 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (20589100572779 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106450147261 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨50, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (20589100572779 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106450147261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_51 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82322712759751 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212904334599 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨51, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82322712759751 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212904334599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_52 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (16457809288249 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (276613539581 / 12500000000000 : ℝ))
      (E := (cell13029 ⟨52, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (16457809288249 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (276613539581 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_53 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (16451080661511 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106456177713 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨53, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (16451080661511 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106456177713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_54 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82221783330777 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212916329243 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨54, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82221783330777 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212916329243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_55 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (41094093241573 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442584070507 / 20000000000000 : ℝ))
      (E := (cell13029 ⟨55, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (41094093241573 / 50000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442584070507 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_56 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (16430922547407 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (138307772641 / 6250000000000 : ℝ))
      (E := (cell13029 ⟨56, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (16430922547407 / 20000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (138307772641 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_57 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (20530265516239 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442585682683 / 20000000000000 : ℝ))
      (E := (cell13029 ⟨57, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (20530265516239 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (442585682683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_58 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (20521883609889 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106466191653 / 50000000000000 : ℝ))
      (E := (cell13029 ⟨58, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (20521883609889 / 25000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (1106466191653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13029_59 : CellCertificate 13029 (54857635697347 / 625000000000000 : ℝ) (322423122511057 / 200000000000000000 : ℝ) (162722293416871 / 5000000000000000 : ℝ)
    (cell13029 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · norm_num [cell13029]
  · have h := gap_lower (n := 13029) (a := (82054029833619 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212936444951 / 100000000000000 : ℝ))
      (E := (cell13029 ⟨59, by decide⟩).energy) (xi := (162722293416871 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13029 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13029]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13029])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13029) (a := (82054029833619 / 100000000000000 : ℝ)) (b := (3951145227 / 2500000000000 : ℝ)) (q := (2212936444951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13029])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13029]

theorem cert13030_40 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (8269456646143 / 10000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212746621967 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨40, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (8269456646143 / 10000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212746621967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_41 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82660643233867 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212750628939 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨41, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82660643233867 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212750628939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_42 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82626743507471 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (5531886647 / 250000000000 : ℝ))
      (E := (cell13030 ⟨42, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82626743507471 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (5531886647 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_43 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82592867252753 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212758651497 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨43, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82592867252753 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212758651497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_44 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (660472115523 / 800000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106381332203 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨44, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (660472115523 / 800000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106381332203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_45 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41262592520571 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553191659249 / 25000000000000 : ℝ))
      (E := (cell13030 ⟨45, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41262592520571 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553191659249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_46 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (8249137902601 / 10000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106385342589 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨46, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (8249137902601 / 10000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106385342589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_47 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41228798183039 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (221277468907 / 10000000000000 : ℝ))
      (E := (cell13030 ⟨47, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41228798183039 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (221277468907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_48 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82423837032591 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106389352643 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨48, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82423837032591 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106389352643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_49 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82390100996937 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (221278273133 / 10000000000000 : ℝ))
      (E := (cell13030 ⟨49, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82390100996937 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (221278273133 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_50 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82356388230647 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (442557341097 / 20000000000000 : ℝ))
      (E := (cell13030 ⟨50, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82356388230647 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (442557341097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_51 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82322698705397 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106395371417 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨51, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82322698705397 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106395371417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_52 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82289032393001 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212794722199 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨52, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82289032393001 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212794722199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_53 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (10281923658177 / 12500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212798758339 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨53, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (10281923658177 / 12500000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212798758339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_54 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (41110884647369 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (34575043573 / 1562500000000 : ℝ))
      (E := (cell13030 ⟨54, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (41110884647369 / 50000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (34575043573 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_55 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82188172453201 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212806809443 / 100000000000000 : ℝ))
      (E := (cell13030 ⟨55, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82188172453201 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (2212806809443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_56 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82154598713181 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (138300676043 / 6250000000000 : ℝ))
      (E := (cell13030 ⟨56, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82154598713181 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (138300676043 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_57 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82121048047187 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (13830092539 / 625000000000 : ℝ))
      (E := (cell13030 ⟨57, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82121048047187 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (13830092539 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_58 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (20521880106967 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553204708231 / 25000000000000 : ℝ))
      (E := (cell13030 ⟨58, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (20521880106967 / 25000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (553204708231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13030_59 : CellCertificate 13030 (877695573650011 / 10000000000000000 : ℝ) (1611991849528377 / 1000000000000000000 : ℝ) (162709515545289 / 5000000000000000 : ℝ)
    (cell13030 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · norm_num [cell13030]
  · have h := gap_lower (n := 13030) (a := (82054015828007 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106411416503 / 50000000000000 : ℝ))
      (E := (cell13030 ⟨59, by decide⟩).energy) (xi := (162709515545289 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13030 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13030]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13030])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13030) (a := (82054015828007 / 100000000000000 : ℝ)) (b := (158033539067 / 100000000000000 : ℝ)) (q := (1106411416503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13030])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13030]

theorem cert13031_40 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (5168409521357 / 6250000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212633058439 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨40, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (5168409521357 / 6250000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212633058439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_41 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (10332578640039 / 12500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212637062223 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨41, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (10332578640039 / 12500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212637062223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_42 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (3305069176003 / 4000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212641088941 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨42, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (3305069176003 / 4000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212641088941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_43 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82592853151511 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212645078541 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨43, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82592853151511 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212645078541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_44 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82559000345281 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212649088401 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨44, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82559000345281 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212649088401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_45 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (40295493629 / 48828125000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106326558441 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨45, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (40295493629 / 48828125000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106326558441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_46 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41245682471599 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (221265710321 / 10000000000000 : ℝ))
      (E := (cell13031 ⟨46, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41245682471599 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (221265710321 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_47 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (412287911447 / 500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553165290783 / 25000000000000 : ℝ))
      (E := (cell13031 ⟨47, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (412287911447 / 500000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553165290783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_48 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82423822962041 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212665117539 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨48, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82423822962041 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212665117539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_49 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (8239008693251 / 10000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442533828153 / 20000000000000 : ℝ))
      (E := (cell13031 ⟨49, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (8239008693251 / 10000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (442533828153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_50 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82356374172339 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106336585579 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨50, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82356374172339 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106336585579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_51 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41161342326601 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106338602901 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨51, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41161342326601 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106338602901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_52 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (16457803669383 / 20000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212681182509 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨52, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (16457803669383 / 20000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212681182509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_53 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41127687612717 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553171304009 / 25000000000000 : ℝ))
      (E := (cell13031 ⟨53, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41127687612717 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553171304009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_54 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (16444351052171 / 20000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106344621901 / 50000000000000 : ℝ))
      (E := (cell13031 ⟨54, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (16444351052171 / 20000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (1106344621901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_55 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82188158425413 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212693262051 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨55, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82188158425413 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212693262051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_56 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41077292345741 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212697266821 / 100000000000000 : ℝ))
      (E := (cell13031 ⟨56, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41077292345741 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (2212697266821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_57 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82121034031573 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (276587656743 / 12500000000000 : ℝ))
      (E := (cell13031 ⟨57, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82121034031573 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (276587656743 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_58 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (41043753209167 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553176319561 / 25000000000000 : ℝ))
      (E := (cell13031 ⟨58, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (41043753209167 / 50000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (553176319561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13031_59 : CellCertificate 13031 (175533796010429 / 2000000000000000 : ℝ) (1611868105502723 / 1000000000000000000 : ℝ) (13015739175747 / 400000000000000 : ℝ)
    (cell13031 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · norm_num [cell13031]
  · have h := gap_lower (n := 13031) (a := (82054001824547 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (221270927599 / 10000000000000 : ℝ))
      (E := (cell13031 ⟨59, by decide⟩).energy) (xi := (13015739175747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13031 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13031]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13031])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13031) (a := (82054001824547 / 100000000000000 : ℝ)) (b := (79010635483 / 50000000000000 : ℝ)) (q := (221270927599 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13031])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13031]

theorem cert13032_40 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (20673634556041 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (34570617959 / 1562500000000 : ℝ))
      (E := (cell13032 ⟨40, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (20673634556041 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (34570617959 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_41 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82660615008927 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442504709999 / 20000000000000 : ℝ))
      (E := (cell13032 ⟨41, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82660615008927 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442504709999 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_42 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82626715294847 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221252751477 / 10000000000000 : ℝ))
      (E := (cell13032 ⟨42, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82626715294847 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221252751477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_43 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (20648209763109 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212531560123 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨43, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (20648209763109 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212531560123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_44 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82558986252353 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212535566957 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨44, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82558986252353 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212535566957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_45 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41262578432703 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106269796229 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨45, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41262578432703 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106269796229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_46 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (1649827017251 / 2000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212543575853 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨46, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (1649827017251 / 2000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212543575853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_47 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (20614392053721 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442509514789 / 20000000000000 : ℝ))
      (E := (cell13032 ⟨47, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (20614392053721 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (442509514789 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_48 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82423808893653 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212551643419 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨48, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82423808893653 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212551643419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_49 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (20597518217561 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106277802441 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨49, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (20597518217561 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106277802441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_50 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82356360116191 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106279816263 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨50, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82356360116191 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106279816263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_51 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82322670603167 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106281832233 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨51, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82322670603167 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106281832233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_52 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (20572251075747 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106283819257 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨52, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (20572251075747 / 25000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106283819257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_53 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (8225536118761 / 10000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221257166943 / 10000000000000 : ℝ))
      (E := (cell13032 ⟨53, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (8225536118761 / 10000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (221257166943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_54 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (82221741229129 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212575694629 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨54, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (82221741229129 / 100000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212575694629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_55 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (4109407219989 / 5000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212579710359 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨55, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (4109407219989 / 5000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212579710359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_56 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (41077285335969 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106291856327 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨56, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (41077285335969 / 50000000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106291856327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_57 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (1283140937783 / 1562500000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106293878263 / 50000000000000 : ℝ))
      (E := (cell13032 ⟨57, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (1283140937783 / 1562500000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (1106293878263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_58 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (10260936551369 / 12500000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212591719267 / 100000000000000 : ℝ))
      (E := (cell13032 ⟨58, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (10260936551369 / 12500000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (2212591719267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13032_59 : CellCertificate 13032 (877642390363051 / 10000000000000000 : ℝ) (402936095118487 / 250000000000000000 : ℝ) (325367931742013 / 10000000000000000 : ℝ)
    (cell13032 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · norm_num [cell13032]
  · have h := gap_lower (n := 13032) (a := (2051349695581 / 2500000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (22125957739 / 1000000000000 : ℝ))
      (E := (cell13032 ⟨59, by decide⟩).energy) (xi := (325367931742013 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13032 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13032]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13032])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13032) (a := (2051349695581 / 2500000000000 : ℝ)) (b := (158009004779 / 100000000000000 : ℝ)) (q := (22125957739 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13032])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13032]

theorem cert13033_40 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (16538904821757 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212406036003 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨40, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (16538904821757 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212406036003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_41 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (8266060089971 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106205016729 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨41, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (8266060089971 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106205016729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_42 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41313350595893 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106207026971 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨42, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41313350595893 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106207026971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_43 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41296412477763 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212418037399 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨43, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41296412477763 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212418037399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_44 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (8255897216159 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212422041207 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨44, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (8255897216159 / 10000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212422041207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_45 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (16505028556157 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212426063729 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨45, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (16505028556157 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212426063729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_46 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (16498267356813 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (221243010311 / 10000000000000 : ℝ))
      (E := (cell13033 ⟨46, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (16498267356813 / 20000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (221243010311 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_47 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82457554142531 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106217049169 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨47, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82457554142531 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106217049169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_48 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41211897413713 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212438106029 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨48, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41211897413713 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212438106029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_49 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82390058810139 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212442123687 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨49, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82390058810139 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212442123687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_50 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82356346062203 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442489229721 / 20000000000000 : ℝ))
      (E := (cell13033 ⟨50, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82356346062203 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (442489229721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_51 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82322656555291 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553112529707 / 25000000000000 : ℝ))
      (E := (cell13033 ⟨51, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82322656555291 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553112529707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_52 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41144495130609 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212454149281 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨52, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41144495130609 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212454149281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_53 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41127673575971 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212458177609 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨53, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41127673575971 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212458177609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_54 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41110863599779 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212462200267 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨54, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41110863599779 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212462200267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_55 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41094065188151 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (4424932427 / 200000000000 : ℝ))
      (E := (cell13033 ⟨55, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41094065188151 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (4424932427 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_56 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82154556654547 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106235106673 / 50000000000000 : ℝ))
      (E := (cell13033 ⟨56, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82154556654547 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (1106235106673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_57 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (20530251501701 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553118548909 / 25000000000000 : ℝ))
      (E := (cell13033 ⟨57, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (20530251501701 / 25000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553118548909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_58 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (41043739202861 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553119553799 / 25000000000000 : ℝ))
      (E := (cell13033 ⟨58, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (41043739202861 / 50000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (553119553799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13033_59 : CellCertificate 13033 (877615804581823 / 10000000000000000 : ℝ) (1611620674437679 / 1000000000000000000 : ℝ) (325342388134573 / 10000000000000000 : ℝ)
    (cell13033 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · norm_num [cell13033]
  · have h := gap_lower (n := 13033) (a := (82053973824083 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212482267517 / 100000000000000 : ℝ))
      (E := (cell13033 ⟨59, by decide⟩).energy) (xi := (325342388134573 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13033 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13033]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13033])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13033) (a := (82053973824083 / 100000000000000 : ℝ)) (b := (157996740503 / 100000000000000 : ℝ)) (q := (2212482267517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13033])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13033]

theorem cert13034_40 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (3307780399823 / 4000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106146259159 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨40, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (3307780399823 / 4000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106146259159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_41 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82660586792661 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (221229651261 / 10000000000000 : ℝ))
      (E := (cell13034 ⟨41, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82660586792661 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (221229651261 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_42 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (20656671772723 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106150264989 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨42, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (20656671772723 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106150264989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_43 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82592810860783 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212304569213 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨43, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82592810860783 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212304569213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_44 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (2579967439781 / 3125000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212308570021 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨44, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (2579967439781 / 3125000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212308570021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_45 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (10315641087291 / 12500000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553078147397 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨45, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (10315641087291 / 12500000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553078147397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_46 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (2577853834617 / 3125000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212316567141 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨46, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (2577853834617 / 3125000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212316567141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_47 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (4122877003617 / 5000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106160309213 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨47, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (4122877003617 / 5000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106160309213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_48 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82423780763361 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (22123246233 / 1000000000000 : ℝ))
      (E := (cell13034 ⟨48, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82423780763361 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (22123246233 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_49 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (16478008950439 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212328638187 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨49, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (16478008950439 / 20000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212328638187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_50 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (41178166005187 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212332660381 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨50, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (41178166005187 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212332660381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_51 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82322642509573 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212336686963 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨51, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82322642509573 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212336686963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_52 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (41144488110803 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (442468131149 / 20000000000000 : ℝ))
      (E := (cell13034 ⟨52, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (41144488110803 / 50000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (442468131149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_53 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82255333118431 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212344681487 / 100000000000000 : ℝ))
      (E := (cell13034 ⟨53, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82255333118431 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (2212344681487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_54 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (5138857073259 / 6250000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553087175401 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨54, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (5138857073259 / 6250000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553087175401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_55 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82188116354979 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106176356171 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨55, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82188116354979 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106176356171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_56 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (8215454263931 / 10000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (110617835487 / 5000000000000 : ℝ))
      (E := (cell13034 ⟨56, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (8215454263931 / 10000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (110617835487 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_57 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82120991997649 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553090187201 / 25000000000000 : ℝ))
      (E := (cell13034 ⟨57, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82120991997649 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (553090187201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_58 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (20521866100661 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (221236476603 / 10000000000000 : ℝ))
      (E := (cell13034 ⟨58, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (20521866100661 / 25000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (221236476603 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13034_59 : CellCertificate 13034 (21939730567689 / 250000000000000 : ℝ) (1611496987389541 / 1000000000000000000 : ℝ) (10166151517823 / 312500000000000 : ℝ)
    (cell13034 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · norm_num [cell13034]
  · have h := gap_lower (n := 13034) (a := (82053959827077 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106184378419 / 50000000000000 : ℝ))
      (E := (cell13034 ⟨59, by decide⟩).energy) (xi := (10166151517823 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13034 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13034]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13034])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13034) (a := (82053959827077 / 100000000000000 : ℝ)) (b := (7899223907 / 5000000000000 : ℝ)) (q := (1106184378419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13034])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13034]

theorem cert13035_40 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (82694495884533 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106089527551 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨40, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (82694495884533 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106089527551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_41 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41330286343889 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212183046257 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨41, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41330286343889 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212183046257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_42 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (16525334598433 / 20000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553046765133 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨42, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (16525334598433 / 20000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553046765133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_43 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (16518559353641 / 20000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212191096721 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨43, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (16518559353641 / 20000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212191096721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_44 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (82558943986559 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212195094529 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨44, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (82558943986559 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212195094529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_45 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (41262557309017 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212199111143 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨45, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (41262557309017 / 50000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212199111143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_46 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (16498261726717 / 20000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212203144707 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨46, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (16498261726717 / 20000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212203144707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_47 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (8245752600431 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553051783553 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨47, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (8245752600431 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553051783553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_48 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (5151485418841 / 6250000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212211136269 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨48, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (5151485418841 / 6250000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212211136269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_49 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (8239003069641 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106107574193 / 50000000000000 : ℝ))
      (E := (cell13035 ⟨49, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (8239003069641 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (1106107574193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_50 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (160852183517 / 195312500000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (138263697991 / 6250000000000 : ℝ))
      (E := (cell13035 ⟨50, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (160852183517 / 195312500000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (138263697991 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_51 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (20580657116503 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212223191761 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨51, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (20580657116503 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212223191761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_52 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (82288962184151 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553056804243 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨52, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (82288962184151 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553056804243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_53 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (20563829771769 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212231240151 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨53, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (20563829771769 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212231240151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_54 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (20555424786721 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (276529407219 / 12500000000000 : ℝ))
      (E := (cell13035 ⟨54, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (20555424786721 / 25000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (276529407219 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_55 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (8218810233581 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212239266019 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨55, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (8218810233581 / 10000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212239266019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_56 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (82154528626227 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212243260991 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨56, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (82154528626227 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212243260991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_57 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (82120977990647 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212247297677 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨57, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (82120977990647 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212247297677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_58 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (82087450401717 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212251312571 / 100000000000000 : ℝ))
      (E := (cell13035 ⟨58, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (82087450401717 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (2212251312571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13035_59 : CellCertificate 13035 (219390661184839 / 2500000000000000 : ℝ) (402843329831291 / 250000000000000000 : ℝ) (325291313048283 / 10000000000000000 : ℝ)
    (cell13035 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · norm_num [cell13035]
  · have h := gap_lower (n := 13035) (a := (82053945832221 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553063825273 / 25000000000000 : ℝ))
      (E := (cell13035 ⟨59, by decide⟩).energy) (xi := (325291313048283 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13035 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13035]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13035])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13035) (a := (82053945832221 / 100000000000000 : ℝ)) (b := (19746527211 / 12500000000000 : ℝ)) (q := (553063825273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13035])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13035]

theorem cert13036_40 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82694481775659 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212065646357 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨40, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82694481775659 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212065646357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_41 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82660558585063 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212069634397 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨41, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82660558585063 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212069634397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_42 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82626658895603 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (442414729121 / 20000000000000 : ℝ))
      (E := (cell13036 ⟨42, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82626658895603 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (442414729121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_43 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (2581024458681 / 3125000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212077678773 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨43, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (2581024458681 / 3125000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212077678773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_44 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82558929902289 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106040836803 / 50000000000000 : ℝ))
      (E := (cell13036 ⟨44, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82558929902289 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106040836803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_45 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82525100539903 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212085687289 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨45, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82525100539903 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212085687289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_46 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82491294561587 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212089717971 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨46, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82491294561587 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212089717971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_47 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41228755969221 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212093704637 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨47, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41228755969221 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212093704637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_48 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82423752641711 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (69128053247 / 3125000000000 : ℝ))
      (E := (cell13036 ⟨48, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82423752641711 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (69128053247 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_49 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (2574688020087 / 3125000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (88484068531 / 4000000000000 : ℝ))
      (E := (cell13036 ⟨49, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (2574688020087 / 3125000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (88484068531 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_50 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (10294537989149 / 12500000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106052865023 / 50000000000000 : ℝ))
      (E := (cell13036 ⟨50, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (10294537989149 / 12500000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106052865023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_51 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82322614424609 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212109751297 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨51, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82322614424609 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212109751297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_52 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (20572237037213 / 25000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (22121137739 / 1000000000000 : ℝ))
      (E := (cell13036 ⟨52, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (20572237037213 / 25000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (22121137739 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_53 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82255305057877 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212117794517 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨53, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82255305057877 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212117794517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_54 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82221685123779 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212121809603 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨54, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82221685123779 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212121809603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_55 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (41094044159397 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212125815401 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨55, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (41094044159397 / 50000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212125815401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_56 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (80229018179 / 97656250000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212129807949 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨56, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (80229018179 / 97656250000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212129807949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_57 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (16424192797159 / 20000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106066921129 / 50000000000000 : ℝ))
      (E := (cell13036 ⟨57, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (16424192797159 / 20000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106066921129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_58 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (82087436402941 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106068927409 / 50000000000000 : ℝ))
      (E := (cell13036 ⟨58, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (82087436402941 / 100000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (1106068927409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13036_59 : CellCertificate 13036 (877536070676311 / 10000000000000000 : ℝ) (805624835120089 / 500000000000000000 : ℝ) (81316445391849 / 2500000000000000 : ℝ)
    (cell13036 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · norm_num [cell13036]
  · have h := gap_lower (n := 13036) (a := (20513482959879 / 25000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212141841053 / 100000000000000 : ℝ))
      (E := (cell13036 ⟨59, by decide⟩).energy) (xi := (81316445391849 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13036 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13036]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13036])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13036) (a := (20513482959879 / 25000000000000 : ℝ)) (b := (157959959147 / 100000000000000 : ℝ)) (q := (2212141841053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13036])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13036]

theorem cert13037_40 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (10336808458619 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105976087263 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨40, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (10336808458619 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105976087263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_41 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41330272242257 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276494527279 / 12500000000000 : ℝ))
      (E := (cell13037 ⟨41, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41330272242257 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276494527279 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_42 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82626644801207 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211960226373 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨42, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82626644801207 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211960226373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_43 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82592768589543 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (55299106413 / 2500000000000 : ℝ))
      (E := (cell13037 ⟨43, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82592768589543 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (55299106413 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_44 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82558915820183 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105984124189 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨44, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82558915820183 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105984124189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_45 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (16505017292787 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211972259133 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨45, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (16505017292787 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211972259133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_46 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (10311410061469 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211976286931 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨46, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (10311410061469 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2211976286931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_47 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41228748937367 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105990135381 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨47, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41228748937367 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105990135381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_48 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41211869292063 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105992133619 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨48, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41211869292063 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1105992133619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_49 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (20597500647829 / 25000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276498541607 / 12500000000000 : ℝ))
      (E := (cell13037 ⟨49, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (20597500647829 / 25000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276498541607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_50 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (41178144933919 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (44239846939 / 2000000000000 : ℝ))
      (E := (cell13037 ⟨50, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (41178144933919 / 50000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (44239846939 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_51 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82322600385363 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276499538317 / 12500000000000 : ℝ))
      (E := (cell13037 ⟨51, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82322600385363 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276499538317 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_52 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82288934115709 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (553000081633 / 25000000000000 : ℝ))
      (E := (cell13037 ⟨52, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82288934115709 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (553000081633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_53 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (5140955689427 / 6250000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2212004344589 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨53, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (5140955689427 / 6250000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2212004344589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_54 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82221671102827 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (55300208929 / 2500000000000 : ℝ))
      (E := (cell13037 ⟨54, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82221671102827 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (55300208929 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_55 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82188074303931 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2212012360489 / 100000000000000 : ℝ))
      (E := (cell13037 ⟨55, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82188074303931 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (2212012360489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_56 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82154500606517 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276502051221 / 12500000000000 : ℝ))
      (E := (cell13037 ⟨56, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82154500606517 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276502051221 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_57 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (10265118747887 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1106010220861 / 50000000000000 : ℝ))
      (E := (cell13037 ⟨57, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (10265118747887 / 12500000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (1106010220861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_58 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (16417484481263 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276503056497 / 12500000000000 : ℝ))
      (E := (cell13037 ⟨58, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (16417484481263 / 20000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (276503056497 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13037_59 : CellCertificate 13037 (10968868756469 / 125000000000000 : ℝ) (402781510032553 / 250000000000000000 : ℝ) (325240254126657 / 10000000000000000 : ℝ)
    (cell13037 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · norm_num [cell13037]
  · have h := gap_lower (n := 13037) (a := (82053917848959 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (44240568719 / 2000000000000 : ℝ))
      (E := (cell13037 ⟨59, by decide⟩).energy) (xi := (325240254126657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13037 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13037]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13037])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13037) (a := (82053917848959 / 100000000000000 : ℝ)) (b := (39486925629 / 25000000000000 : ℝ)) (q := (44240568719 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13037])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13037]

theorem cert13038_40 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (20673613391103 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105919407973 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨40, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (20673613391103 / 25000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105919407973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_41 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (8266053038613 / 10000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105921398881 / 50000000000000 : ℝ))
      (E := (cell13038 ⟨41, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (8266053038613 / 10000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (1105921398881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_42 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (3305065228359 / 4000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552961700709 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨42, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (3305065228359 / 4000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552961700709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_43 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41296377251729 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552962707491 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨43, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41296377251729 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552962707491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_44 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (1031986271753 / 1250000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (55296371943 / 2500000000000 : ℝ))
      (E := (cell13038 ⟨44, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (1031986271753 / 1250000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (55296371943 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_45 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (5157817024383 / 6250000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552964721393 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨45, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (5157817024383 / 6250000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552964721393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_46 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82491266424077 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (276482856449 / 12500000000000 : ℝ))
      (E := (cell13038 ⟨46, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82491266424077 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (276482856449 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_47 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41228741906593 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (221186689153 / 10000000000000 : ℝ))
      (E := (cell13038 ⟨47, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41228741906593 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (221186689153 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_48 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (824237245287 / 1000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211870885239 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨48, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (824237245287 / 1000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211870885239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_49 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82389988542007 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211874889147 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨49, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82389988542007 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211874889147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_50 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (8042605061 / 9765625000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442375780109 / 20000000000000 : ℝ))
      (E := (cell13038 ⟨50, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (8042605061 / 9765625000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442375780109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_51 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82322586348273 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442376583303 / 20000000000000 : ℝ))
      (E := (cell13038 ⟨51, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82322586348273 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442376583303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_52 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82288920084721 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211886933929 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨52, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82288920084721 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211886933929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_53 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82255277005941 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (44237818989 / 2000000000000 : ℝ))
      (E := (cell13038 ⟨53, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82255277005941 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (44237818989 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_54 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82221657084029 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (221189495953 / 10000000000000 : ℝ))
      (E := (cell13038 ⟨54, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82221657084029 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (221189495953 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_55 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82188060291221 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442379803909 / 20000000000000 : ℝ))
      (E := (cell13038 ⟨55, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82188060291221 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442379803909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_56 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82154486599889 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (34560984489 / 1562500000000 : ℝ))
      (E := (cell13038 ⟨56, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82154486599889 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (34560984489 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_57 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (41060467991273 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211907036897 / 100000000000000 : ℝ))
      (E := (cell13038 ⟨57, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (41060467991273 / 50000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (2211907036897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_58 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (82087408411839 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552977761211 / 25000000000000 : ℝ))
      (E := (cell13038 ⟨58, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (82087408411839 / 100000000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (552977761211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13038_59 : CellCertificate 13038 (877482934262081 / 10000000000000000 : ℝ) (805501214495451 / 500000000000000000 : ℝ) (6504294614501 / 200000000000000 : ℝ)
    (cell13038 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · norm_num [cell13038]
  · have h := gap_lower (n := 13038) (a := (10256737982569 / 12500000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442383005311 / 20000000000000 : ℝ))
      (E := (cell13038 ⟨59, by decide⟩).energy) (xi := (6504294614501 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13038 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13038]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13038])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13038) (a := (10256737982569 / 12500000000000 : ℝ)) (b := (31587089559 / 20000000000000 : ℝ)) (q := (442383005311 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13038])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13038]

theorem cert13039_40 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41347219731019 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105862726531 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨40, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41347219731019 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105862726531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_41 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (10332564536239 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221172943179 / 10000000000000 : ℝ))
      (E := (cell13039 ⟨41, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (10332564536239 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221172943179 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_42 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82626616618907 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211733433823 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨42, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82626616618907 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211733433823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_43 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (5162046276221 / 6250000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (442347491591 / 20000000000000 : ℝ))
      (E := (cell13039 ⟨43, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (5162046276221 / 6250000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (442347491591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_44 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82558887662459 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105870751381 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨44, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82558887662459 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105870751381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_45 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82525058318483 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221174550771 / 10000000000000 : ℝ))
      (E := (cell13039 ⟨45, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82525058318483 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221174550771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_46 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82491252358563 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (34558586403 / 1562500000000 : ℝ))
      (E := (cell13039 ⟨46, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82491252358563 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (34558586403 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_47 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (41228734876899 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105876753999 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨47, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (41228734876899 / 50000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105876753999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_48 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (10302963809429 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (34558710921 / 1562500000000 : ℝ))
      (E := (cell13039 ⟨48, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (10302963809429 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (34558710921 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_49 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (10298746811857 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105880779561 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨49, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (10298746811857 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105880779561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_50 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (205890654459 / 250000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221176556787 / 10000000000000 : ℝ))
      (E := (cell13039 ⟨50, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (205890654459 / 250000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (221176556787 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_51 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82322572313339 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552942395309 / 25000000000000 : ℝ))
      (E := (cell13039 ⟨51, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82322572313339 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552942395309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_52 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82288906055889 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552943399023 / 25000000000000 : ℝ))
      (E := (cell13039 ⟨52, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82288906055889 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (552943399023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_53 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (16451052596641 / 20000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211777609101 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨53, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (16451052596641 / 20000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211777609101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_54 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (16444328613477 / 20000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105890808357 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨54, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (16444328613477 / 20000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105890808357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_55 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82188046280663 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211785615179 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨55, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82188046280663 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211785615179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_56 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82154472595413 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105894829843 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨56, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82154472595413 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105894829843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_57 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82120921984147 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211793627781 / 100000000000000 : ℝ))
      (E := (cell13039 ⟨57, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82120921984147 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (2211793627781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_58 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (10260924302439 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105898816711 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨58, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (10260924302439 / 12500000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105898816711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13039_59 : CellCertificate 13039 (877456371909093 / 10000000000000000 : ℝ) (1610878836817879 / 1000000000000000000 : ℝ) (325189211361557 / 10000000000000000 : ℝ)
    (cell13039 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · norm_num [cell13039]
  · have h := gap_lower (n := 13039) (a := (82053889874293 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105900836049 / 50000000000000 : ℝ))
      (E := (cell13039 ⟨59, by decide⟩).energy) (xi := (325189211361557 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13039 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13039]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13039])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13039) (a := (82053889874293 / 100000000000000 : ℝ)) (b := (157923194983 / 100000000000000 : ℝ)) (q := (1105900836049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13039])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13039]

theorem cert13040_40 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82694425361829 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211612085873 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨40, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82694425361829 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211612085873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_41 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41330251097929 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105808030757 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨41, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41330251097929 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105808030757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_42 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (20656650632751 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552905029833 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨42, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (20656650632751 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552905029833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_43 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41296363168889 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552906035123 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨43, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41296363168889 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552906035123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_44 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (2063971839671 / 2500000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105814061751 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨44, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (2063971839671 / 2500000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105814061751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_45 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82525044248999 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211632125547 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨45, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82525044248999 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211632125547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_46 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82491238295209 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552909036193 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨46, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82491238295209 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552909036193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_47 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (10307181962071 / 12500000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211640179113 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨47, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (10307181962071 / 12500000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211640179113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_48 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82423696424323 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552911041829 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨48, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82423696424323 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552911041829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_49 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41194980224931 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211648165809 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨49, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41194980224931 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211648165809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_50 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (20589061936179 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105826115449 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨50, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (20589061936179 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105826115449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_51 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (1029031978507 / 1250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211656241661 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨51, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (1029031978507 / 1250000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211656241661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_52 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (8228889202921 / 10000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211660253961 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨52, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (8228889202921 / 10000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211660253961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_53 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41127624481311 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105832132229 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨53, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41127624481311 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105832132229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_54 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (20555407263223 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211668269607 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨54, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (20555407263223 / 25000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211668269607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_55 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (642094002127 / 781250000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552918066413 / 25000000000000 : ℝ))
      (E := (cell13040 ⟨55, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (642094002127 / 781250000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (552918066413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_56 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (1283663415517 / 1562500000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (442335261557 / 20000000000000 : ℝ))
      (E := (cell13040 ⟨56, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (1283663415517 / 1562500000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (442335261557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_57 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41060453993949 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (138230017097 / 6250000000000 : ℝ))
      (E := (cell13040 ⟨57, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41060453993949 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (138230017097 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_58 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (41043690214667 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105842168057 / 50000000000000 : ℝ))
      (E := (cell13040 ⟨58, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (41043690214667 / 50000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (1105842168057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13040_59 : CellCertificate 13040 (438714906728827 / 5000000000000000 : ℝ) (1610755263606779 / 1000000000000000000 : ℝ) (162581848017581 / 5000000000000000 : ℝ)
    (cell13040 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · norm_num [cell13040]
  · have h := gap_lower (n := 13040) (a := (82053875890181 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211688313353 / 100000000000000 : ℝ))
      (E := (cell13040 ⟨59, by decide⟩).energy) (xi := (162581848017581 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13040 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13040]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13040])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13040) (a := (82053875890181 / 100000000000000 : ℝ)) (b := (157910944081 / 100000000000000 : ℝ)) (q := (2211688313353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13040])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13040]

theorem cert13041_40 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41347205631893 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (55287469329 / 2500000000000 : ℝ))
      (E := (cell13041 ⟨40, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41347205631893 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (55287469329 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_41 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82660488103969 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105751372869 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨41, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82660488103969 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105751372869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_42 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82626588445263 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211506800541 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨42, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82626588445263 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211506800541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_43 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82592712258181 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211510759881 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨43, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82592712258181 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211510759881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_44 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82558859513383 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442302959763 / 20000000000000 : ℝ))
      (E := (cell13041 ⟨44, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82558859513383 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442302959763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_45 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (20631257545419 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211518797981 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨45, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (20631257545419 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211518797981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_46 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41245612117007 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (276440351797 / 12500000000000 : ℝ))
      (E := (cell13041 ⟨46, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41245612117007 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (276440351797 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_47 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41228720820749 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211526845929 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨47, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41228720820749 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211526845929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_48 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (20605920593843 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211530831393 / 100000000000000 : ℝ))
      (E := (cell13041 ⟨48, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (20605920593843 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (2211530831393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_49 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (5149371650439 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105767443091 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨49, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (5149371650439 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105767443091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_50 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (20589058426997 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (69110590301 / 3125000000000 : ℝ))
      (E := (cell13041 ⟨50, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (20589058426997 / 25000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (69110590301 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_51 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (5145159015621 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105771448897 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨51, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (5145159015621 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105771448897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_52 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41144439002343 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (138221681721 / 6250000000000 : ℝ))
      (E := (cell13041 ⟨52, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41144439002343 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (138221681721 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_53 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (1285238046003 / 1562500000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552887728881 / 25000000000000 : ℝ))
      (E := (cell13041 ⟨53, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (1285238046003 / 1562500000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552887728881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_54 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (10277701880069 / 12500000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (34555545597 / 1562500000000 : ℝ))
      (E := (cell13041 ⟨54, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (10277701880069 / 12500000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (34555545597 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_55 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82188018266001 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442311782367 / 20000000000000 : ℝ))
      (E := (cell13041 ⟨55, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82188018266001 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442311782367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_56 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (5134652787057 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552890737899 / 25000000000000 : ℝ))
      (E := (cell13041 ⟨56, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (5134652787057 / 6250000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552890737899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_57 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (41060446996899 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442313394843 / 20000000000000 : ℝ))
      (E := (cell13041 ⟨57, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (41060446996899 / 50000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (442313394843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_58 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (16417473288261 / 20000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552892743829 / 25000000000000 : ℝ))
      (E := (cell13041 ⟨58, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (16417473288261 / 20000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (552892743829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13041_59 : CellCertificate 13041 (438701629453431 / 5000000000000000 : ℝ) (805315854676619 / 500000000000000000 : ℝ) (20321136546553 / 625000000000000 : ℝ)
    (cell13041 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · norm_num [cell13041]
  · have h := gap_lower (n := 13041) (a := (82053861908217 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105787504773 / 50000000000000 : ℝ))
      (E := (cell13041 ⟨59, by decide⟩).energy) (xi := (20321136546553 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13041 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13041]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13041])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13041) (a := (82053861908217 / 100000000000000 : ℝ)) (b := (157898695087 / 100000000000000 : ℝ)) (q := (1105787504773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13041])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13041]

theorem cert13042_40 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82694397167907 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105692728073 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨40, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82694397167907 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105692728073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_41 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82660474014243 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105694712831 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨41, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82660474014243 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105694712831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_42 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41313287180843 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (276424184681 / 12500000000000 : ℝ))
      (E := (cell13042 ⟨42, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41313287180843 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (276424184681 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_43 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41296349090373 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (221139749267 / 10000000000000 : ℝ))
      (E := (cell13042 ⟨43, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41296349090373 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (221139749267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_44 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41279422721043 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (221140146983 / 10000000000000 : ℝ))
      (E := (cell13042 ⟨44, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41279422721043 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (221140146983 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_45 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (2578906753641 / 3125000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (276425690627 / 12500000000000 : ℝ))
      (E := (cell13042 ⟨45, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (2578906753641 / 3125000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (276425690627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_46 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41245605087489 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211409538603 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨46, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41245605087489 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211409538603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_47 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (16491485517717 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211413508451 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨47, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (16491485517717 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211413508451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_48 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82423668328577 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105708775071 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨48, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82423668328577 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105708775071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_49 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82389932366343 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211421543271 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨49, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82389932366343 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211421543271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_50 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (16471243934683 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105712772037 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨50, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (16471243934683 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105712772037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_51 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82322530221467 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211429608671 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨51, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82322530221467 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211429608671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_52 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (16457772796463 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105716807941 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨52, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (16457772796463 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105716807941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_53 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (16451044185583 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211437621383 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨53, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (16451044185583 / 20000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211437621383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_54 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82221601030363 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552860405407 / 25000000000000 : ℝ))
      (E := (cell13042 ⟨54, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82221601030363 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (552860405407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_55 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (10273500532737 / 12500000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (110572280643 / 5000000000000 : ℝ))
      (E := (cell13042 ⟨55, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (10273500532737 / 12500000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (110572280643 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_56 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82154430594887 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211449650273 / 100000000000000 : ℝ))
      (E := (cell13042 ⟨56, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82154430594887 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (2211449650273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_57 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (41060440000923 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (221145367059 / 10000000000000 : ℝ))
      (E := (cell13042 ⟨57, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (41060440000923 / 50000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (221145367059 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_58 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (82087352455423 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442291533887 / 20000000000000 : ℝ))
      (E := (cell13042 ⟨58, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (82087352455423 / 100000000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (442291533887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13042_59 : CellCertificate 13042 (175475341651163 / 2000000000000000 : ℝ) (50328380439153 / 31250000000000000 : ℝ) (203195423431 / 6250000000000 : ℝ)
    (cell13042 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · norm_num [cell13042]
  · have h := gap_lower (n := 13042) (a := (205134619821 / 250000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105730850727 / 50000000000000 : ℝ))
      (E := (cell13042 ⟨59, by decide⟩).energy) (xi := (203195423431 / 6250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13042 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13042]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13042])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13042) (a := (205134619821 / 250000000000 : ℝ)) (b := (157886448001 / 100000000000000 : ℝ)) (q := (1105730850727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13042])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13042]

theorem cert13043_40 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (5168398942137 / 6250000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211272134831 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨40, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (5168398942137 / 6250000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211272134831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_41 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82660459926681 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (276409520011 / 12500000000000 : ℝ))
      (E := (cell13043 ⟨41, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82660459926681 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (276409520011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_42 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (8262656028027 / 10000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552820052221 / 25000000000000 : ℝ))
      (E := (cell13043 ⟨42, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (8262656028027 / 10000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (552820052221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_43 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82592684105473 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211284221159 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨43, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82592684105473 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211284221159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_44 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (1651176627459 / 2000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211288195421 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨44, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (1651176627459 / 2000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211288195421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_45 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (20631250513377 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105646123877 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨45, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (20631250513377 / 25000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105646123877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_46 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82491196118101 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105648129267 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨46, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82491196118101 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105648129267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_47 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (8245741353783 / 10000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (110565011281 / 5000000000000 : ℝ))
      (E := (cell13043 ⟨47, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (8245741353783 / 10000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (110565011281 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_48 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82423654283939 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211304264597 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨48, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82423654283939 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211304264597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_49 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82389918327817 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211308255057 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨49, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82389918327817 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211308255057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_50 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82356205640997 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (8845249249 / 400000000000 : ℝ))
      (E := (cell13043 ⟨50, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82356205640997 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (8845249249 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_51 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82322516195151 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211316315257 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨51, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82322516195151 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211316315257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_52 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (5143053122631 / 6250000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211320319937 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨52, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (5143053122631 / 6250000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211320319937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_53 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82255206913789 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211324322953 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨53, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82255206913789 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211324322953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_54 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (41110793511163 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105664160379 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨54, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (41110793511163 / 50000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105664160379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_55 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82187990259941 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211332368729 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨55, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82187990259941 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211332368729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_56 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (8215441659901 / 10000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211336344663 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨56, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (8215441659901 / 10000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211336344663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_57 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82120866012043 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105670181339 / 50000000000000 : ℝ))
      (E := (cell13043 ⟨57, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82120866012043 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (1105670181339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_58 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (10260917308961 / 12500000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (221134441847 / 10000000000000 : ℝ))
      (E := (cell13043 ⟨58, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (10260917308961 / 12500000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (221134441847 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13043_59 : CellCertificate 13043 (438675080751807 / 5000000000000000 : ℝ) (161038465770139 / 100000000000000000 : ℝ) (81271793567101 / 2500000000000000 : ℝ)
    (cell13043 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · norm_num [cell13043]
  · have h := gap_lower (n := 13043) (a := (82053833950729 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211348389077 / 100000000000000 : ℝ))
      (E := (cell13043 ⟨59, by decide⟩).energy) (xi := (81271793567101 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13043 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13043]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13043])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13043) (a := (82053833950729 / 100000000000000 : ℝ)) (b := (157874202823 / 100000000000000 : ℝ)) (q := (2211348389077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13043])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13043]

theorem cert13044_40 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82694368982641 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442231773599 / 20000000000000 : ℝ))
      (E := (cell13044 ⟨40, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82694368982641 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (442231773599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_41 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82660445841281 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276395361277 / 12500000000000 : ℝ))
      (E := (cell13044 ⟨41, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82660445841281 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (276395361277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_42 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82626546201017 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (110558346801 / 5000000000000 : ℝ))
      (E := (cell13044 ⟨42, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82626546201017 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (110558346801 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_43 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82592670032361 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211170945351 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨43, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82592670032361 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211170945351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_44 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82558817305973 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552793729179 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨44, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82558817305973 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552793729179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_45 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41262493996331 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552794741549 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨45, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41262493996331 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552794741549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_46 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41245591031691 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211182974169 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨46, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41245591031691 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211182974169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_47 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (5153587468077 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (6909959367 / 312500000000 : ℝ))
      (E := (cell13044 ⟨47, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (5153587468077 / 6250000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (6909959367 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_48 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41211820120729 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105595487379 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨48, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41211820120729 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105595487379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_49 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82389904291447 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211195021541 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨49, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82389904291447 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211195021541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_50 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82356191610733 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105599508561 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨50, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82356191610733 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105599508561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_51 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (20580625542747 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211203017553 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨51, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (20580625542747 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211203017553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_52 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (8228883594403 / 10000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552801769691 / 25000000000000 : ℝ))
      (E := (cell13044 ⟨52, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (8228883594403 / 10000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (552801769691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_53 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (16451038580363 / 20000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211211079319 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨53, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (16451038580363 / 20000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211211079319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_54 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41110786508219 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (221121507471 / 10000000000000 : ℝ))
      (E := (cell13044 ⟨54, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41110786508219 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (221121507471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_55 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (10273497032517 / 12500000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (110560953059 / 5000000000000 : ℝ))
      (E := (cell13044 ⟨55, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (10273497032517 / 12500000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (110560953059 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_56 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (41077201302641 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105611546961 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨56, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (41077201302641 / 50000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105611546961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_57 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (82120852024387 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211227109661 / 100000000000000 : ℝ))
      (E := (cell13044 ⟨57, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (82120852024387 / 100000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (2211227109661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_58 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (820873244901 / 1000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105615552009 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨58, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (820873244901 / 1000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105615552009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13044_59 : CellCertificate 13044 (219330904662339 / 2500000000000000 : ℝ) (1610261160294361 / 1000000000000000000 : ℝ) (325061675080243 / 10000000000000000 : ℝ)
    (cell13044 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · norm_num [cell13044]
  · have h := gap_lower (n := 13044) (a := (20513454993801 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105617565821 / 50000000000000 : ℝ))
      (E := (cell13044 ⟨59, by decide⟩).energy) (xi := (325061675080243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13044 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13044]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13044])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13044) (a := (20513454993801 / 25000000000000 : ℝ)) (b := (1233296559 / 781250000000 : ℝ)) (q := (1105617565821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13044])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13044]

theorem cert13045_40 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41347177446627 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105522827819 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨40, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41347177446627 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105522827819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_41 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82660431758043 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (69095302339 / 3125000000000 : ℝ))
      (E := (cell13045 ⟨41, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82660431758043 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (69095302339 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_42 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20656633030981 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (110552682943 / 5000000000000 : ℝ))
      (E := (cell13045 ⟨42, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20656633030981 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (110552682943 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_43 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82592655961409 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211057665247 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨43, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82592655961409 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211057665247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_44 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20639700810289 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552765423147 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨44, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20639700810289 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552765423147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_45 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (10315621741747 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (55276643481 / 2500000000000 : ℝ))
      (E := (cell13045 ⟨45, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (10315621741747 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (55276643481 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_46 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (4124558400541 / 5000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (138191859027 / 6250000000000 : ℝ))
      (E := (cell13045 ⟨46, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (4124558400541 / 5000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (138191859027 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_47 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82457385442791 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105536882483 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨47, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82457385442791 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105536882483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_48 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20605906550283 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (442215547919 / 20000000000000 : ℝ))
      (E := (cell13045 ⟨48, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20605906550283 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (442215547919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_49 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82389890257231 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105540891867 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨49, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82389890257231 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105540891867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_50 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41178088791311 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105542888359 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨50, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41178088791311 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105542888359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_51 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82322488148979 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552772443649 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨51, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82322488148979 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552772443649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_52 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (20572205482029 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105546916651 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨52, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (20572205482029 / 25000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105546916651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_53 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (10281897361499 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552774457849 / 25000000000000 : ℝ))
      (E := (cell13045 ⟨53, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (10281897361499 / 12500000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (552774457849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_54 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82221559012701 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211101824373 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨54, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82221559012701 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211101824373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_55 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (1027349528281 / 1250000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211105867607 / 100000000000000 : ℝ))
      (E := (cell13045 ⟨55, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (1027349528281 / 1250000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (2211105867607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_56 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41077194306851 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (138194364931 / 6250000000000 : ℝ))
      (E := (cell13045 ⟨56, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41077194306851 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (138194364931 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_57 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (82120838038879 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105556926179 / 50000000000000 : ℝ))
      (E := (cell13045 ⟨57, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (82120838038879 / 100000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (1105556926179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_58 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (41043655255329 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (276389737961 / 12500000000000 : ℝ))
      (E := (cell13045 ⟨58, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (41043655255329 / 50000000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (276389737961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13045_59 : CellCertificate 13045 (438648539846071 / 5000000000000000 : ℝ) (402534420456863 / 250000000000000000 : ℝ) (40629522490513 / 1250000000000000 : ℝ)
    (cell13045 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · norm_num [cell13045]
  · have h := gap_lower (n := 13045) (a := (2564181437557 / 3125000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (44222438583 / 2000000000000 : ℝ))
      (E := (cell13045 ⟨59, by decide⟩).energy) (xi := (40629522490513 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13045 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13045]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13045])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13045) (a := (2564181437557 / 3125000000000 : ℝ)) (b := (39462429547 / 25000000000000 : ℝ)) (q := (44222438583 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13045])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13045]

theorem cert13046_40 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82694340806029 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (442186487797 / 20000000000000 : ℝ))
      (E := (cell13046 ⟨40, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82694340806029 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (442186487797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_41 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (10332552209621 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210936455183 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨41, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (10332552209621 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210936455183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_42 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82626518048993 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221094043623 / 10000000000000 : ℝ))
      (E := (cell13046 ⟨42, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82626518048993 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221094043623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_43 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (10324080236577 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210944498549 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨43, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (10324080236577 / 12500000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210944498549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_44 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (41279394589249 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (442189692833 / 20000000000000 : ℝ))
      (E := (cell13046 ⟨44, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (41279394589249 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (442189692833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_45 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82524959877447 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210952507991 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨45, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82524959877447 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210952507991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_46 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (2577848561263 / 3125000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105478255201 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨46, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (2577848561263 / 3125000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105478255201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_47 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (41228685699253 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210960528201 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨47, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (41228685699253 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210960528201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_48 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82423612162961 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (552741139777 / 25000000000000 : ℝ))
      (E := (cell13046 ⟨48, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82423612162961 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (552741139777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_49 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (8238987622517 / 10000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210968541637 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨49, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (8238987622517 / 10000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210968541637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_50 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (16471232711333 / 20000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210972591039 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨50, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (16471232711333 / 20000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210972591039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_51 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82322474129121 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221097658639 / 10000000000000 : ℝ))
      (E := (cell13046 ⟨51, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82322474129121 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (221097658639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_52 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (41144403957177 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (17273285809 / 781250000000 : ℝ))
      (E := (cell13046 ⟨52, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (41144403957177 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (17273285809 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_53 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82255164884319 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (552746144797 / 25000000000000 : ℝ))
      (E := (cell13046 ⟨53, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82255164884319 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (552746144797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_54 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82221545011113 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (110549431443 / 5000000000000 : ℝ))
      (E := (cell13046 ⟨54, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82221545011113 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (110549431443 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_55 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82187948266973 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105496305309 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨55, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82187948266973 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105496305309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_56 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (8215437462427 / 10000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210996638741 / 100000000000000 : ℝ))
      (E := (cell13046 ⟨56, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (8215437462427 / 10000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (2210996638741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_57 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (41060412027759 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (44220012999 / 2000000000000 : ℝ))
      (E := (cell13046 ⟨57, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (41060412027759 / 50000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (44220012999 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_58 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82087296533363 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105502349537 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨58, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82087296533363 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105502349537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13046_59 : CellCertificate 13046 (27414704519721 / 312500000000000 : ℝ) (322002844459261 / 200000000000000000 : ℝ) (81252672199743 / 2500000000000000 : ℝ)
    (cell13046 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · norm_num [cell13046]
  · have h := gap_lower (n := 13046) (a := (82053792030589 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105504361189 / 50000000000000 : ℝ))
      (E := (cell13046 ⟨59, by decide⟩).energy) (xi := (81252672199743 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13046 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13046]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13046])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13046) (a := (82053792030589 / 100000000000000 : ℝ)) (b := (15783747873 / 10000000000000 : ℝ)) (q := (1105504361189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13046])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13046]

theorem cert13047_40 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41347163360483 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (442163843607 / 20000000000000 : ℝ))
      (E := (cell13047 ⟨40, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41347163360483 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (442163843607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_41 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82660403598053 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210823231223 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨41, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82660403598053 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210823231223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_42 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41313251988111 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210827268131 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨42, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41313251988111 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210827268131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_43 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82592627825983 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (442166253741 / 20000000000000 : ℝ))
      (E := (cell13047 ⟨43, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82592627825983 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (442166253741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_44 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82558775117999 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210835290323 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨44, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82558775117999 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210835290323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_45 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (3300997832923 / 4000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210839331347 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨45, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (3300997832923 / 4000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210839331347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_46 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (10311392489021 / 12500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210843331 / 100000000000 : ℝ))
      (E := (cell13047 ⟨46, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (10311392489021 / 12500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210843331 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_47 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (10307169669547 / 12500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (221084734609 / 10000000000000 : ℝ))
      (E := (cell13047 ⟨47, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (10307169669547 / 12500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (221084734609 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_48 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (2575737441467 / 3125000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210851374333 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨48, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (2575737441467 / 3125000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210851374333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_49 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41194931097631 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105427677121 / 50000000000000 : ℝ))
      (E := (cell13047 ⟨49, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41194931097631 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105427677121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_50 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82356149532861 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210859401071 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨50, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82356149532861 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210859401071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_51 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (10290307513927 / 12500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (442172678779 / 20000000000000 : ℝ))
      (E := (cell13047 ⟨51, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (10290307513927 / 12500000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (442172678779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_52 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41144396951371 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210867388577 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨52, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41144396951371 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210867388577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_53 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (20563787719699 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (69089732527 / 3125000000000 : ℝ))
      (E := (cell13047 ⟨53, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (20563787719699 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (69089732527 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_54 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (3288861240467 / 4000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210875429061 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨54, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (3288861240467 / 4000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210875429061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_55 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82187934273613 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210879467609 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨55, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82187934273613 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210879467609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_56 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (16430872127397 / 20000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210883434303 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨56, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (16430872127397 / 20000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210883434303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_57 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (41060405037151 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105443721631 / 50000000000000 : ℝ))
      (E := (cell13047 ⟨57, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (41060405037151 / 50000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (1105443721631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_58 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (20521820639553 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (110544574509 / 5000000000000 : ℝ))
      (E := (cell13047 ⟨58, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (20521820639553 / 25000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (110544574509 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13047_59 : CellCertificate 13047 (438622006732623 / 5000000000000000 : ℝ) (321978156339313 / 200000000000000000 : ℝ) (162492600851917 / 5000000000000000 : ℝ)
    (cell13047 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · norm_num [cell13047]
  · have h := gap_lower (n := 13047) (a := (82053778061499 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210895511323 / 100000000000000 : ℝ))
      (E := (cell13047 ⟨59, by decide⟩).energy) (xi := (162492600851917 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13047 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13047]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13047])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13047) (a := (82053778061499 / 100000000000000 : ℝ)) (b := (78912620589 / 50000000000000 : ℝ)) (q := (2210895511323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13047])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13047]

theorem cert13048_40 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (16538862527613 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210706051569 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨40, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (16538862527613 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210706051569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_41 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82660389521299 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210710061771 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨41, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82660389521299 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210710061771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_42 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (8262648990561 / 10000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (110535704787 / 5000000000000 : ℝ))
      (E := (cell13048 ⟨42, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (8262648990561 / 10000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (110535704787 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_43 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82592613761509 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210718093419 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨43, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82592613761509 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210718093419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_44 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82558761059657 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210722112189 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨44, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82558761059657 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210722112189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_45 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82524931770861 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210726150411 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨45, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82524931770861 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210726150411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_46 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (20622781466519 / 25000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210730147309 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨46, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (20622781466519 / 25000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210730147309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_47 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82457343316401 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210734159689 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨47, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82457343316401 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210734159689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_48 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (41211792046541 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552684546317 / 25000000000000 : ℝ))
      (E := (cell13048 ⟨48, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (41211792046541 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (552684546317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_49 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (20597462041877 / 25000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210742162559 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨49, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (20597462041877 / 25000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210742162559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_50 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82356135511209 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210746206817 / 100000000000000 : ℝ))
      (E := (cell13048 ⟨50, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82356135511209 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (2210746206817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_51 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (41161223047931 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (442150039423 / 20000000000000 : ℝ))
      (E := (cell13048 ⟨51, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (41161223047931 / 50000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (442150039423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_52 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82288779893281 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105377124189 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨52, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82288779893281 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105377124189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_53 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82255136875423 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (221075823917 / 10000000000000 : ℝ))
      (E := (cell13048 ⟨53, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82255136875423 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (221075823917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_54 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (16444303402877 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (276345285511 / 12500000000000 : ℝ))
      (E := (cell13048 ⟨54, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (16444303402877 / 20000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (276345285511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_55 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82187920282401 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105383130593 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨55, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82187920282401 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105383130593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_56 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82154346651847 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105385142369 / 50000000000000 : ℝ))
      (E := (cell13048 ⟨56, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82154346651847 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (1105385142369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_57 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82120796095233 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (221077429147 / 10000000000000 : ℝ))
      (E := (cell13048 ⟨57, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82120796095233 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (221077429147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_58 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82087268585207 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (138173646013 / 6250000000000 : ℝ))
      (E := (cell13048 ⟨58, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82087268585207 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (138173646013 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13048_59 : CellCertificate 13048 (219304371548441 / 2500000000000000 : ℝ) (804883680011939 / 500000000000000000 : ℝ) (324959718637677 / 10000000000000000 : ℝ)
    (cell13048 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · norm_num [cell13048]
  · have h := gap_lower (n := 13048) (a := (82053764094553 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (138173897201 / 6250000000000 : ℝ))
      (E := (cell13048 ⟨59, by decide⟩).energy) (xi := (324959718637677 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13048 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13048]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13048])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13048) (a := (82053764094553 / 100000000000000 : ℝ)) (b := (157813005531 / 100000000000000 : ℝ)) (q := (138173897201 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13048])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13048]

theorem cert13049_40 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (3307771942293 / 4000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210592939587 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨40, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (3307771942293 / 4000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210592939587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_41 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41330187723353 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210596946827 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨41, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41330187723353 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210596946827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_42 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41313237918579 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210600919053 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨42, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41313237918579 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210600919053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_43 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41296299849597 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210604972689 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨43, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41296299849597 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210604972689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_44 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82558747003473 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552652247159 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨44, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82558747003473 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552652247159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_45 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82524917720803 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (34540827581 / 1562500000000 : ℝ))
      (E := (cell13049 ⟨45, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82524917720803 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (34540827581 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_46 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82491111822139 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (276327127281 / 12500000000000 : ℝ))
      (E := (cell13049 ⟨46, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82491111822139 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (276327127281 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_47 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82457329278581 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105310513971 / 50000000000000 : ℝ))
      (E := (cell13049 ⟨47, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82457329278581 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (1105310513971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_48 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41211785030687 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210625050881 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨48, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41211785030687 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210625050881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_49 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41194917070953 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (110531451279 / 5000000000000 : ℝ))
      (E := (cell13049 ⟨49, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41194917070953 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (110531451279 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_50 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82356121491709 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (221063306729 / 10000000000000 : ℝ))
      (E := (cell13049 ⟨50, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82356121491709 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (221063306729 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_51 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (41161216041229 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210637055087 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨51, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (41161216041229 / 50000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210637055087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_52 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82288765885969 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (442128220779 / 20000000000000 : ℝ))
      (E := (cell13049 ⟨52, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82288765885969 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (442128220779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_53 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82255122874199 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552661273069 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨53, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82255122874199 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552661273069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_54 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82221503019243 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210649134831 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨54, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82221503019243 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210649134831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_55 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82187906293337 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (221065310961 / 10000000000000 : ℝ))
      (E := (cell13049 ⟨55, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82187906293337 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (221065310961 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_56 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (16430866533771 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552664282723 / 25000000000000 : ℝ))
      (E := (cell13049 ⟨56, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (16430866533771 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (552664282723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_57 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (20530195529577 / 25000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210661135399 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨57, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (20530195529577 / 25000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210661135399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_58 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (16417450922869 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210665177957 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨58, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (16417450922869 / 20000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210665177957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

theorem cert13049_59 : CellCertificate 13049 (54824435175983 / 625000000000000 : ℝ) (1609643957273891 / 1000000000000000000 : ℝ) (2538548746871 / 78125000000000 : ℝ)
    (cell13049 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · norm_num [cell13049]
  · have h := gap_lower (n := 13049) (a := (82053750129749 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210669194831 / 100000000000000 : ℝ))
      (E := (cell13049 ⟨59, by decide⟩).energy) (xi := (2538548746871 / 78125000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13049 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13049]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13049])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13049) (a := (82053750129749 / 100000000000000 : ℝ)) (b := (15780077179 / 10000000000000 : ℝ)) (q := (2210669194831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13049])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13049]

end BstLean.Part268
