import BstLean.Part268CellShard17Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12775_40 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82695897523697 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (89700740411 / 4000000000000 : ℝ))
      (E := (cell12775 ⟨40, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82695897523697 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (89700740411 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_41 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (516636973843 / 625000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560630638159 / 25000000000000 : ℝ))
      (E := (cell12775 ⟨41, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (516636973843 / 625000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560630638159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_42 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82627957687603 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (70078954381 / 3125000000000 : ℝ))
      (E := (cell12775 ⟨42, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82627957687603 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (70078954381 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_43 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (10324252889029 / 12500000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (224253053077 / 10000000000000 : ℝ))
      (E := (cell12775 ⟨43, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (10324252889029 / 12500000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (224253053077 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_44 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82560112059281 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (224253452323 / 10000000000000 : ℝ))
      (E := (cell12775 ⟨44, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82560112059281 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (224253452323 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_45 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41263112249707 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121269287541 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨45, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41263112249707 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121269287541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_46 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82492360403441 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242542567029 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨46, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82492360403441 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242542567029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_47 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (1030731496779 / 1250000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (224254655613 / 10000000000000 : ℝ))
      (E := (cell12775 ⟨47, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (1030731496779 / 1250000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (224254655613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_48 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82424702487153 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242550540379 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨48, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82424702487153 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242550540379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_49 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82390908609189 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242554576521 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨49, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82390908609189 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242554576521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_50 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82357138079819 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (280319825401 / 12500000000000 : ℝ))
      (E := (cell12775 ⟨50, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82357138079819 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (280319825401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_51 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82323390870579 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242562558781 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨51, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82323390870579 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242562558781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_52 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (20572416738287 / 25000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242566617423 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨52, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (20572416738287 / 25000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242566617423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_53 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82255966299343 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (224257059903 / 10000000000000 : ℝ))
      (E := (cell12775 ⟨53, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82255966299343 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (224257059903 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_54 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41111144440563 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242574618423 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨54, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41111144440563 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242574618423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_55 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82188634670597 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (56064465327 / 2500000000000 : ℝ))
      (E := (cell12775 ⟨55, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82188634670597 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (56064465327 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_56 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (16431000727999 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (56064565961 / 2500000000000 : ℝ))
      (E := (cell12775 ⟨56, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (16431000727999 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (56064565961 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_57 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41060697880849 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121293315759 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨57, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41060697880849 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121293315759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_58 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82087811008221 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448518129477 / 20000000000000 : ℝ))
      (E := (cell12775 ⟨58, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82087811008221 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448518129477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_59 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41027124676109 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560648655649 / 25000000000000 : ℝ))
      (E := (cell12775 ⟨59, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41027124676109 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560648655649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12776_40 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82695894918467 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (44847965621 / 2000000000000 : ℝ))
      (E := (cell12776 ⟨40, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82695894918467 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (44847965621 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_41 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82661913509577 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (224240226321 / 10000000000000 : ℝ))
      (E := (cell12776 ⟨41, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82661913509577 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (224240226321 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_42 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82627955681813 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242406250009 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨42, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82627955681813 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242406250009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_43 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82594021405543 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448482059869 / 20000000000000 : ℝ))
      (E := (cell12776 ⟨43, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82594021405543 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448482059869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_44 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82560110651281 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (70075446639 / 3125000000000 : ℝ))
      (E := (cell12776 ⟨44, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82560110651281 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (70075446639 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_45 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82526223389691 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242418286759 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨45, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82526223389691 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242418286759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_46 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (16498471918317 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242422280701 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨46, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (16498471918317 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242422280701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_47 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (1030731490349 / 1250000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242426272483 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨47, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (1030731490349 / 1250000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242426272483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_48 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82424702269801 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (7007594747 / 312500000000 : ℝ))
      (E := (cell12776 ⟨48, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82424702269801 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (7007594747 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_49 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (20597727172119 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (224243430029 / 10000000000000 : ℝ))
      (E := (cell12776 ⟨49, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (20597727172119 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (224243430029 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_50 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41178569227669 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242438331711 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨50, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41178569227669 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242438331711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_51 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41161695770961 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242442292703 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨51, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41161695770961 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242442292703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_52 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82289667919909 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (280305787301 / 12500000000000 : ℝ))
      (E := (cell12776 ⟨52, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82289667919909 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (280305787301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_53 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82255967561117 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448490069167 / 20000000000000 : ℝ))
      (E := (cell12776 ⟨53, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82255967561117 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448490069167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_54 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82222290437507 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242454313609 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨54, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82222290437507 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242454313609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_55 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41094318260591 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242458375493 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨55, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41094318260591 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242458375493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_56 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (4107750289219 / 5000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242462350547 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨56, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (4107750289219 / 5000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242462350547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_57 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (2053034954987 / 2500000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121233176553 / 50000000000000 : ℝ))
      (E := (cell12776 ⟨57, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (2053034954987 / 2500000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121233176553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_58 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41043906869499 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560617594783 / 25000000000000 : ℝ))
      (E := (cell12776 ⟨58, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41043906869499 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560617594783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_59 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (20513563093897 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242474365181 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨59, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (20513563093897 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242474365181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12777_40 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (8269589231409 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242277989963 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨40, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (8269589231409 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242277989963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_41 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82661911205091 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242282029493 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨41, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82661911205091 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242282029493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_42 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (16525590735361 / 20000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (448457203119 / 20000000000000 : ℝ))
      (E := (cell12777 ⟨42, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (16525590735361 / 20000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (448457203119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_43 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82594019699599 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242290006099 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨43, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82594019699599 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242290006099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_44 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82560109243989 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560573514677 / 25000000000000 : ℝ))
      (E := (cell12777 ⟨44, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82560109243989 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560573514677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_45 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82526222280641 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121149027193 / 50000000000000 : ℝ))
      (E := (cell12777 ⟨45, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82526222280641 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121149027193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_46 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41246179390183 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242302050383 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨46, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41246179390183 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242302050383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_47 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41229259357061 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (448461208981 / 20000000000000 : ℝ))
      (E := (cell12777 ⟨47, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41229259357061 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (448461208981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_48 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41212351026507 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121155017973 / 50000000000000 : ℝ))
      (E := (cell12777 ⟨48, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41212351026507 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121155017973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_49 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82390908768293 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (8969256321 / 400000000000 : ℝ))
      (E := (cell12777 ⟨49, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82390908768293 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (8969256321 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_50 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (1647142776627 / 2000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242318057477 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨50, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (1647142776627 / 2000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242318057477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_51 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (20580848053431 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121161041467 / 50000000000000 : ℝ))
      (E := (cell12777 ⟨51, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (20580848053431 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121161041467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_52 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82289668887093 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242326094801 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨52, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82289668887093 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242326094801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_53 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41127984411639 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (224233009001 / 10000000000000 : ℝ))
      (E := (cell12777 ⟨53, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41127984411639 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (224233009001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_54 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82222291994241 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242334124367 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨54, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82222291994241 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242334124367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_55 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82188638372083 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (44846762707 / 2000000000000 : ℝ))
      (E := (cell12777 ⟨55, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82188638372083 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (44846762707 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_56 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41077503964523 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (70073191227 / 3125000000000 : ℝ))
      (E := (cell12777 ⟨56, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41077503964523 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (70073191227 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_57 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (20530350159377 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242346131363 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨57, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (20530350159377 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242346131363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_58 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41043908234993 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (224235010843 / 10000000000000 : ℝ))
      (E := (cell12777 ⟨58, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41043908234993 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (224235010843 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_59 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41027127699567 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242354164553 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨59, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41027127699567 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242354164553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12778_40 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (41347944855283 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242157813283 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨40, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (41347944855283 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242157813283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_41 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82661908901421 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242161792709 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨41, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82661908901421 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242161792709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_42 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82627951672577 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242165836953 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨42, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82627951672577 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242165836953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_43 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (103242522493 / 125000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242169827509 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨43, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (103242522493 / 125000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242169827509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_44 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82560107837407 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242173822011 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨44, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82560107837407 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242173822011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_45 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (10315777646533 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121088909547 / 50000000000000 : ℝ))
      (E := (cell12778 ⟨45, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (10315777646533 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121088909547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_46 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82492357969783 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242181876079 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨46, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82492357969783 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242181876079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_47 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (3298340728037 / 4000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242185873401 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨47, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (3298340728037 / 4000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242185873401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_48 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82424701836793 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242189867929 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨48, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82424701836793 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242189867929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_49 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82390908848639 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121096928719 / 50000000000000 : ℝ))
      (E := (cell12778 ⟨49, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82390908848639 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121096928719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_50 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82357139207857 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560549474621 / 25000000000000 : ℝ))
      (E := (cell12778 ⟨50, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82357139207857 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560549474621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_51 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (2572606027687 / 3125000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242201870467 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨51, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (2572606027687 / 3125000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242201870467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_52 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (822896698547 / 1000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (224220588853 / 10000000000000 : ℝ))
      (E := (cell12778 ⟨52, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (822896698547 / 1000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (224220588853 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_53 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (41127985042913 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242209890619 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨53, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (41127985042913 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242209890619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_54 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (41111146775663 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560553468363 / 25000000000000 : ℝ))
      (E := (cell12778 ⟨54, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (41111146775663 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560553468363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_55 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82188640223301 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560554473163 / 25000000000000 : ℝ))
      (E := (cell12778 ⟨55, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82188640223301 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560554473163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_56 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82155010073993 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242221944593 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨56, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82155010073993 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242221944593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_57 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (41060701537891 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242225907137 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨57, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (41060701537891 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242225907137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_58 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (2565244350037 / 3125000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242229953637 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨58, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (2565244350037 / 3125000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242229953637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_59 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (10256782302857 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448446792303 / 20000000000000 : ℝ))
      (E := (cell12778 ⟨59, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (10256782302857 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448446792303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12779_40 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (16539177421579 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121018816749 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨40, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (16539177421579 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121018816749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_41 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82661906598569 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121020835207 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨41, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82661906598569 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121020835207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_42 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82627949669129 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121022827641 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨42, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82627949669129 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121022827641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_43 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (16518803257989 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (280256205741 / 12500000000000 : ℝ))
      (E := (cell12779 ⟨43, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (16518803257989 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (280256205741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_44 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82560106431533 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242053641207 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨44, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82560106431533 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242053641207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_45 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82526220064559 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560514424657 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨45, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82526220064559 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560514424657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_46 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82492357159837 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560515424723 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨46, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82492357159837 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560515424723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_47 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (10307314711041 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560516424763 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨47, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (10307314711041 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560516424763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_48 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82424701621137 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121034848551 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨48, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82424701621137 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121034848551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_49 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (16478181785903 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121036845409 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨49, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (16478181785903 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121036845409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_50 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82357139584857 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121038838883 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨50, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82357139584857 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121038838883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_51 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41161696779351 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242081714313 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨51, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41161696779351 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242081714313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_52 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82289670822729 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121042869317 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨52, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82289670822729 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121042869317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_53 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41127985674381 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242089747659 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨53, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41127985674381 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242089747659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_54 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82222295108763 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242093738113 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨54, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82222295108763 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242093738113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_55 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (16437728414967 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121048853253 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨55, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (16437728414967 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121048853253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_56 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82155012219221 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560525441851 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨56, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82155012219221 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560525441851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_57 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82121405514301 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (35032902181 / 1562500000000 : ℝ))
      (E := (cell12779 ⟨57, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82121405514301 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (35032902181 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_58 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82087821932593 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (112105486861 / 5000000000000 : ℝ))
      (E := (cell12779 ⟨58, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82087821932593 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (112105486861 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_59 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82054261446753 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242113756067 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨59, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82054261446753 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242113756067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12780_40 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (3307835380243 / 4000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241917509367 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨40, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (3307835380243 / 4000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241917509367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_41 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (20665476074133 / 25000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (560480371569 / 25000000000000 : ℝ))
      (E := (cell12780 ⟨41, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (20665476074133 / 25000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (560480371569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_42 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41313973833231 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241925529383 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨42, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41313973833231 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241925529383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_43 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41297007293117 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (112096476009 / 5000000000000 : ℝ))
      (E := (cell12780 ⟨43, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41297007293117 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (112096476009 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_44 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41280052513183 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241933516297 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨44, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41280052513183 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241933516297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_45 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41263109478763 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241937516371 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨45, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41263109478763 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241937516371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_46 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (1288943067977 / 1562500000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120970759411 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨46, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (1288943067977 / 1562500000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120970759411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_47 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (20614629294083 / 25000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241945521857 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨47, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (20614629294083 / 25000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241945521857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_48 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41212350703023 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120974761733 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨48, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41212350703023 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120974761733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_49 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (2059772725273 / 2500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241953580393 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨49, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (2059772725273 / 2500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241953580393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_50 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82357139962351 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (560489393073 / 25000000000000 : ℝ))
      (E := (cell12780 ⟨50, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82357139962351 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (560489393073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_51 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41161697115939 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241961555459 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨51, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41161697115939 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241961555459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_52 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82289671791181 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241965586073 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨52, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82289671791181 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241965586073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_53 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (16451194522417 / 20000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120984801037 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨53, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (16451194522417 / 20000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120984801037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_54 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (10277787083319 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241973600183 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨54, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (10277787083319 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241973600183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_55 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41094321963343 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (140123598557 / 6250000000000 : ℝ))
      (E := (cell12780 ⟨55, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41094321963343 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (140123598557 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_56 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82155014364731 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (140123849231 / 6250000000000 : ℝ))
      (E := (cell12780 ⟨56, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82155014364731 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (140123849231 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_57 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82121407953067 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120992814351 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨57, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82121407953067 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120992814351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_58 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82087824664213 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (280248704589 / 12500000000000 : ℝ))
      (E := (cell12780 ⟨58, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82087824664213 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (280248704589 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_59 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (3282170578833 / 4000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (224199360741 / 10000000000000 : ℝ))
      (E := (cell12780 ⟨59, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (3282170578833 / 4000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (224199360741 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12781_40 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (20673970476277 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560449345533 / 25000000000000 : ℝ))
      (E := (cell12781 ⟨40, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (20673970476277 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560449345533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_41 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (5166368874707 / 6250000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241801416629 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨41, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (5166368874707 / 6250000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241801416629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_42 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (3305117826583 / 4000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (280225675057 / 12500000000000 : ℝ))
      (E := (cell12781 ⟨42, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (3305117826583 / 4000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (280225675057 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_43 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82594012883267 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (28022617393 / 1250000000000 : ℝ))
      (E := (cell12781 ⟨43, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82594012883267 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (28022617393 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_44 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (20640025905477 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140113336777 / 6250000000000 : ℝ))
      (E := (cell12781 ⟨44, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (20640025905477 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140113336777 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_45 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (41263108925583 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560454347517 / 25000000000000 : ℝ))
      (E := (cell12781 ⟨45, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (41263108925583 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560454347517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_46 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (16498471108371 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140113837173 / 6250000000000 : ℝ))
      (E := (cell12781 ⟨46, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (16498471108371 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140113837173 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_47 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82458516664937 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241825400737 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨47, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82458516664937 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241825400737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_48 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82424701191519 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120914702983 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨48, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82424701191519 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120914702983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_49 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (16478181818571 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (448366693439 / 20000000000000 : ℝ))
      (E := (cell12781 ⟨49, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (16478181818571 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (448366693439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_50 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82357140340339 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120918732041 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨50, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82357140340339 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120918732041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_51 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (10290424363189 / 12500000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241841452921 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨51, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (10290424363189 / 12500000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241841452921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_52 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (10286209095007 / 12500000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (44836908617 / 2000000000000 : ℝ))
      (E := (cell12781 ⟨52, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (10286209095007 / 12500000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (44836908617 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_53 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (41127986937897 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241849453863 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨53, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (41127986937897 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241849453863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_54 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (20555574556173 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140115841229 / 6250000000000 : ℝ))
      (E := (cell12781 ⟨54, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (20555574556173 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140115841229 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_55 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82188645778853 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241857503873 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨55, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82188645778853 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241857503873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_56 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82155016510521 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120930732301 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨56, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82155016510521 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120930732301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_57 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82121410392077 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241865515341 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨57, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82121410392077 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241865515341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_58 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82087827396043 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120934737291 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨58, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82087827396043 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120934737291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_59 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (2564195859221 / 3125000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120936757773 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨59, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (2564195859221 / 3125000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120936757773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12782_40 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (82695879304993 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (280209663819 / 12500000000000 : ℝ))
      (E := (cell12782 ⟨40, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (82695879304993 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (280209663819 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_41 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (82661899694907 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (112084064257 / 5000000000000 : ℝ))
      (E := (cell12782 ⟨41, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (82661899694907 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (112084064257 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_42 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (82627943663467 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (280210665913 / 12500000000000 : ℝ))
      (E := (cell12782 ⟨42, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (82627943663467 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (280210665913 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_43 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (20648502795261 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448337863707 / 20000000000000 : ℝ))
      (E := (cell12782 ⟨43, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (20648502795261 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448337863707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_44 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41280051109079 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120846658231 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨44, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41280051109079 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120846658231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_45 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41263108372739 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (56042432993 / 2500000000000 : ℝ))
      (E := (cell12782 ⟨45, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41263108372739 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (56042432993 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_46 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41246177366909 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (224170132673 / 10000000000000 : ℝ))
      (E := (cell12782 ⟨46, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41246177366909 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (224170132673 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_47 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41229258077071 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241705335693 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨47, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41229258077071 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241705335693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_48 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41212350488779 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (11208546723 / 500000000000 : ℝ))
      (E := (cell12782 ⟨48, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41212350488779 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (11208546723 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_49 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41195454587659 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560428337807 / 25000000000000 : ℝ))
      (E := (cell12782 ⟨49, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41195454587659 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560428337807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_50 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (4117857035941 / 5000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241717353139 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨50, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (4117857035941 / 5000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241717353139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_51 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (20580848894901 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560430336921 / 25000000000000 : ℝ))
      (E := (cell12782 ⟨51, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (20580848894901 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560430336921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_52 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (82289673729353 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (7005391847 / 312500000000 : ℝ))
      (E := (cell12782 ⟨52, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (82289673729353 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (7005391847 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_53 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (82255975139891 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120864681043 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨53, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (82255975139891 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120864681043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_54 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (82222299783183 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (56043334391 / 2500000000000 : ℝ))
      (E := (cell12782 ⟨54, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (82222299783183 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (56043334391 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_55 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (10273580953917 / 12500000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241737428281 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨55, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (10273580953917 / 12500000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241737428281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_56 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (82155018656591 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241741398123 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨56, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (82155018656591 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241741398123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_57 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41060706415667 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241745399497 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨57, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41060706415667 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241745399497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_58 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41043915064041 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560437357091 / 25000000000000 : ℝ))
      (E := (cell12782 ⟨58, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41043915064041 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560437357091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_59 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (16410854103899 / 20000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241753421273 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨59, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (16410854103899 / 20000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241753421273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12783_40 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (8269587670573 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241557235871 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨40, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (8269587670573 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241557235871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_41 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41330948697659 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (140097579259 / 6250000000000 : ℝ))
      (E := (cell12783 ⟨41, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41330948697659 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (140097579259 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_42 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82627941663139 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120782625563 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨42, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82627941663139 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120782625563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_43 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (20648502369891 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241569242641 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨43, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (20648502369891 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241569242641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_44 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (20640025203779 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241573300389 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨44, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (20640025203779 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241573300389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_45 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82526215640461 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (224157730533 / 10000000000000 : ℝ))
      (E := (cell12783 ⟨45, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82526215640461 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (224157730533 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_46 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82492353926417 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (560395328677 / 25000000000000 : ℝ))
      (E := (cell12783 ⟨46, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82492353926417 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (560395328677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_47 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82458515643947 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120792633903 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨47, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82458515643947 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120792633903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_48 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (1006160898 / 1220703125 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (224158928043 / 10000000000000 : ℝ))
      (E := (cell12783 ⟨48, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (1006160898 / 1220703125 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (224158928043 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_49 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (8239090925831 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120796645729 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨49, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (8239090925831 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120796645729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_50 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41178570548897 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (560399324613 / 25000000000000 : ℝ))
      (E := (cell12783 ⟨50, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41178570548897 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (560399324613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_51 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82323396254153 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (448320259753 / 20000000000000 : ℝ))
      (E := (cell12783 ⟨51, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82323396254153 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (448320259753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_52 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82289674699071 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241605348571 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨52, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82289674699071 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241605348571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_53 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41127988202187 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241609326747 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨53, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41127988202187 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241609326747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_54 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41111150671013 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (140100834257 / 6250000000000 : ℝ))
      (E := (cell12783 ⟨54, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41111150671013 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (140100834257 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_55 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41094324742067 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241617350139 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨55, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41094324742067 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241617350139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_56 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82155020802943 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (280202666141 / 12500000000000 : ℝ))
      (E := (cell12783 ⟨56, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82155020802943 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (280202666141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_57 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (16424283054167 / 20000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (224162534033 / 10000000000000 : ℝ))
      (E := (cell12783 ⟨57, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (16424283054167 / 20000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (224162534033 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_58 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (20521958215083 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120814689851 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨58, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (20521958215083 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120814689851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_59 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (20513568386023 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120816691897 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨59, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (20513568386023 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120816691897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12784_40 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (82695874107317 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (140089826053 / 6250000000000 : ℝ))
      (E := (cell12784 ⟨40, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (82695874107317 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (140089826053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_41 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (82661895096543 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (280180156011 / 12500000000000 : ℝ))
      (E := (cell12784 ⟨41, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (82661895096543 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (280180156011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_42 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (8262793966359 / 10000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (89657809229 / 4000000000000 : ℝ))
      (E := (cell12784 ⟨42, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (8262793966359 / 10000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (89657809229 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_43 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (20648501944707 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (448289844517 / 20000000000000 : ℝ))
      (E := (cell12784 ⟨43, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (20648501944707 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (448289844517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_44 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (4128004970639 / 5000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (448290656273 / 20000000000000 : ℝ))
      (E := (cell12784 ⟨44, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (4128004970639 / 5000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (448290656273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_45 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (20631553634029 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (280182161003 / 12500000000000 : ℝ))
      (E := (cell12784 ⟨45, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (20631553634029 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (280182161003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_46 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (20623088279913 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (140091327557 / 6250000000000 : ℝ))
      (E := (cell12784 ⟨46, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (20623088279913 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (140091327557 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_47 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (5153657195897 / 6250000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120732627999 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨47, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (5153657195897 / 6250000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120732627999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_48 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (82424700551327 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241469272397 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨48, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (82424700551327 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241469272397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_49 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (8239090934183 / 10000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120736643943 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨49, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (8239090934183 / 10000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120736643943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_50 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (4117857073863 / 5000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (89659092001 / 4000000000000 : ℝ))
      (E := (cell12784 ⟨50, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (4117857073863 / 5000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (89659092001 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_51 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (2058084923229 / 2500000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241481306163 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨51, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (2058084923229 / 2500000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241481306163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_52 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (20572418917303 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241485303441 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨52, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (20572418917303 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241485303441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_53 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (82255977669243 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (448297857757 / 20000000000000 : ℝ))
      (E := (cell12784 ⟨53, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (82255977669243 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (448297857757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_54 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (4111115145061 / 5000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120746658999 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨54, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (4111115145061 / 5000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120746658999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_55 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (2568395354289 / 3125000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241497328553 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨55, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (2568395354289 / 3125000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241497328553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_56 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41077511474787 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (8966005267 / 400000000000 : ℝ))
      (E := (cell12784 ⟨56, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41077511474787 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (8966005267 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_57 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41060708855291 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120752668919 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨57, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41060708855291 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120752668919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_58 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (10260979449099 / 12500000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120754664299 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨58, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (10260979449099 / 12500000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120754664299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_59 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (2564196142777 / 3125000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (224151334391 / 10000000000000 : ℝ))
      (E := (cell12784 ⟨59, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (2564196142777 / 3125000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (224151334391 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12785_40 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (20673967877439 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (56032931337 / 2500000000000 : ℝ))
      (E := (cell12785 ⟨40, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (20673967877439 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (56032931337 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_41 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (10332736599823 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241321224969 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨41, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (10332736599823 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241321224969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_42 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (4131396883241 / 5000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241325266101 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨42, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (4131396883241 / 5000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241325266101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_43 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (16518801215767 / 20000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448265851673 / 20000000000000 : ℝ))
      (E := (cell12785 ⟨43, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (16518801215767 / 20000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448265851673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_44 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (5160006125697 / 6250000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560333314847 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨44, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (5160006125697 / 6250000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560333314847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_45 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41263106716221 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560334316951 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨45, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41263106716221 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560334316951 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_46 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41246176156761 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (224134128203 / 10000000000000 : ℝ))
      (E := (cell12785 ⟨46, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41246176156761 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (224134128203 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_47 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82458514625357 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241345300267 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨47, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82458514625357 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241345300267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_48 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41212350169529 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241349261559 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨48, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41212350169529 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241349261559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_49 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82390909425879 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448270656309 / 20000000000000 : ℝ))
      (E := (cell12785 ⟨49, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82390909425879 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448270656309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_50 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (4117857092861 / 5000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (140084831179 / 6250000000000 : ℝ))
      (E := (cell12785 ⟨50, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (4117857092861 / 5000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (140084831179 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_51 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82323397604623 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241361310867 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨51, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82323397604623 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241361310867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_52 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41144838319887 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241365314689 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨52, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41144838319887 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241365314689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_53 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82255978934499 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (112068465363 / 5000000000000 : ℝ))
      (E := (cell12785 ⟨53, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82255978934499 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (112068465363 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_54 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (20555576115191 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241373344381 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨54, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (20555576115191 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241373344381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_55 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41094326595339 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560344340881 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨55, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41094326595339 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560344340881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_56 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41077512548243 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560345340247 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨56, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41077512548243 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560345340247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_57 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41060710075287 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560346333217 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨57, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41060710075287 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560346333217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_58 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41043919162731 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560347333557 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨58, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41043919162731 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560347333557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_59 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82054279593811 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241393360819 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨59, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82054279593811 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241393360819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12786_40 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41347934456523 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (448239457403 / 20000000000000 : ℝ))
      (E := (cell12786 ⟨40, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41347934456523 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (448239457403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_41 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (258318407817 / 312500000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241201316347 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨41, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (258318407817 / 312500000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241201316347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_42 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (20656983916707 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120602649227 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨42, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (20656983916707 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120602649227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_43 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (1290531318431 / 1562500000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (56030232279 / 2500000000000 : ℝ))
      (E := (cell12786 ⟨43, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (1290531318431 / 1562500000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (56030232279 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_44 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82560096610231 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (8754739427 / 390625000000 : ℝ))
      (E := (cell12786 ⟨44, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82560096610231 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (8754739427 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_45 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82526212329439 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (280152162943 / 12500000000000 : ℝ))
      (E := (cell12786 ⟨45, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82526212329439 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (280152162943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_46 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82492351508027 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (140076332517 / 6250000000000 : ℝ))
      (E := (cell12786 ⟨46, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82492351508027 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (140076332517 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_47 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82458514116961 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241225341697 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨47, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82458514116961 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241225341697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_48 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (10303087515919 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120614653431 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨48, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (10303087515919 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120614653431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_49 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (10298863688807 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560308332851 / 25000000000000 : ℝ))
      (E := (cell12786 ⟨49, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (10298863688807 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560308332851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_50 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (10294642779709 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560309338491 / 25000000000000 : ℝ))
      (E := (cell12786 ⟨50, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (10294642779709 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560309338491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_51 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (2572606196267 / 3125000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241241371889 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨51, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (2572606196267 / 3125000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241241371889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_52 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41144838805379 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241245382317 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨52, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41144838805379 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241245382317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_53 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82255980200141 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120624691087 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨53, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82255980200141 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120624691087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_54 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (4111115301033 / 5000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120626684089 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨54, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (4111115301033 / 5000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120626684089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_55 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82188655044423 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120628697973 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨55, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82188655044423 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120628697973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_56 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41077513621839 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120630701357 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨56, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41077513621839 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120630701357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_57 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (8212142259081 / 10000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (17509885817 / 781250000000 : ℝ))
      (E := (cell12786 ⟨57, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (8212142259081 / 10000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (17509885817 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_58 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41043920529171 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560317349149 / 25000000000000 : ℝ))
      (E := (cell12786 ⟨58, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41043920529171 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560317349149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_59 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82054282618933 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120636717263 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨59, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82054282618933 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120636717263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12787_40 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41347933158593 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241077376209 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨40, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41347933158593 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241077376209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_41 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (8266188820511 / 10000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241081345887 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨41, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (8266188820511 / 10000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241081345887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_42 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (5164245854351 / 6250000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120542693293 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨42, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (5164245854351 / 6250000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120542693293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_43 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (20648500670269 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120544689897 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨43, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (20648500670269 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120544689897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_44 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (2580002975313 / 3125000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (70034168223 / 3125000000000 : ℝ))
      (E := (cell12787 ⟨44, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (2580002975313 / 3125000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (70034168223 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_45 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41263105613553 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448219479049 / 20000000000000 : ℝ))
      (E := (cell12787 ⟨45, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41263105613553 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448219479049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_46 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82492350703167 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448220282907 / 20000000000000 : ℝ))
      (E := (cell12787 ⟨46, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82492350703167 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448220282907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_47 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (16491702721833 / 20000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241105380287 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨47, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (16491702721833 / 20000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241105380287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_48 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (8242469991621 / 10000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120554704153 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨48, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (8242469991621 / 10000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120554704153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_49 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82390909595561 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241113378497 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨49, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82390909595561 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241113378497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_50 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82357142618617 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241117406333 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨50, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82357142618617 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241117406333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_51 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41161699478461 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120560715109 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨51, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41161699478461 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120560715109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_52 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82289678582163 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (280140680911 / 12500000000000 : ℝ))
      (E := (cell12787 ⟨52, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82289678582163 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (280140680911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_53 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (10281997683271 / 12500000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241129454469 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨53, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (10281997683271 / 12500000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241129454469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_54 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41111153790453 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560283362119 / 25000000000000 : ℝ))
      (E := (cell12787 ⟨54, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41111153790453 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560283362119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_55 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (20547164224621 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120568712909 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨55, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (20547164224621 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120568712909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_56 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (1643100587823 / 2000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241141441927 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨56, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (1643100587823 / 2000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241141441927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_57 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82121425031291 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241145492963 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨57, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82121425031291 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241145492963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_58 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82087843791431 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (89645978261 / 4000000000000 : ℝ))
      (E := (cell12787 ⟨58, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82087843791431 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (89645978261 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_59 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82054285644229 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560288376457 / 25000000000000 : ℝ))
      (E := (cell12787 ⟨59, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82054285644229 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560288376457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12788_40 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82695863722177 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240957462307 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨40, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82695863722177 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240957462307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_41 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (16532377181919 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120480715573 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨41, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (16532377181919 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120480715573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_42 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82627931673181 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240965471697 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨42, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82627931673181 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240965471697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_43 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82594000983311 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120484732721 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨43, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82594000983311 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120484732721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_44 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (20640023452627 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (224097347001 / 10000000000000 : ℝ))
      (E := (cell12788 ⟨44, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (20640023452627 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (224097347001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_45 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (16505242025089 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (8753818297 / 390625000000 : ℝ))
      (E := (cell12788 ⟨45, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (16505242025089 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (8753818297 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_46 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41246174949471 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120490752961 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨46, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41246174949471 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120490752961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_47 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82458513101967 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240985474959 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨47, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82458513101967 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240985474959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_48 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (2575771865801 / 3125000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120494753473 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨48, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (2575771865801 / 3125000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120494753473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_49 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82390909681193 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (35015523153 / 1562500000000 : ℝ))
      (E := (cell12788 ⟨49, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82390909681193 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (35015523153 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_50 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82357143000053 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560249378741 / 25000000000000 : ℝ))
      (E := (cell12788 ⟨50, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82357143000053 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560249378741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_51 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (20580849908439 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241001544869 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨51, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (20580849908439 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241001544869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_52 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (8228967955399 / 10000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241005509601 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨52, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (8228967955399 / 10000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241005509601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_53 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41127991366291 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241009524141 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨53, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41127991366291 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241009524141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_54 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41111154570751 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241013526189 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨54, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41111154570751 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241013526189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_55 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82188658752859 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (14006359821 / 625000000000 : ℝ))
      (E := (cell12788 ⟨55, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82188658752859 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (14006359821 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_56 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41077515769451 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241021537759 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨56, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41077515769451 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241021537759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_57 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82121427472017 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120512769859 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨57, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82121427472017 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120512769859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_58 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82087846524729 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (280128696649 / 12500000000000 : ℝ))
      (E := (cell12788 ⟨58, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82087846524729 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (280128696649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_59 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82054288669699 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241033574727 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨59, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82054288669699 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2241033574727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12789_40 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82695861128017 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560209401017 / 25000000000000 : ℝ))
      (E := (cell12789 ⟨40, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82695861128017 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560209401017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_41 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41330941807447 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240841572127 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨41, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41330941807447 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240841572127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_42 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (3305117187101 / 4000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240845612589 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨42, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (3305117187101 / 4000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240845612589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_43 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82593999286287 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120424803467 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨43, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82593999286287 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120424803467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_44 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41280046205853 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560213403197 / 25000000000000 : ℝ))
      (E := (cell12789 ⟨44, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41280046205853 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560213403197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_45 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41263104512227 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240857628783 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨45, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41263104512227 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240857628783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_46 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (10311543636919 / 12500000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (448172318887 / 20000000000000 : ℝ))
      (E := (cell12789 ⟨46, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (10311543636919 / 12500000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (448172318887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_47 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82458512595369 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120432812857 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨47, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82458512595369 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120432812857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_48 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (1287885929619 / 1562500000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240869661731 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨48, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (1287885929619 / 1562500000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240869661731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_49 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82390909767353 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240873641289 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨49, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82390909767353 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240873641289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_50 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41178571690991 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240877620867 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨50, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41178571690991 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240877620867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_51 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82323400311047 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240881656827 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨51, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82323400311047 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240881656827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_52 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82289680526237 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (280110710917 / 12500000000000 : ℝ))
      (E := (cell12789 ⟨52, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82289680526237 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (280110710917 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_53 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82255983999381 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240889650257 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨53, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82255983999381 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240889650257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_54 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (5138894418903 / 6250000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (448178732081 / 20000000000000 : ℝ))
      (E := (cell12789 ⟨54, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (5138894418903 / 6250000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (448178732081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_55 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (1643773212151 / 2000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120448827623 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨55, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (1643773212151 / 2000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120448827623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_56 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41077516843467 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560225422553 / 25000000000000 : ℝ))
      (E := (cell12789 ⟨56, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41077516843467 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560225422553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_57 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (20530357478247 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240905702309 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨57, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (20530357478247 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240905702309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_58 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82087849258237 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (112045484371 / 5000000000000 : ℝ))
      (E := (cell12789 ⟨58, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82087849258237 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (112045484371 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_59 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (5128393230959 / 6250000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (280114212553 / 12500000000000 : ℝ))
      (E := (cell12789 ⟨59, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (5128393230959 / 6250000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (280114212553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12790_40 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (20673964633677 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240717742731 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨40, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (20673964633677 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240717742731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_41 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41330940660503 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (224072176883 / 10000000000000 : ℝ))
      (E := (cell12790 ⟨41, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41330940660503 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (224072176883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_42 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41313963841323 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (112036287523 / 5000000000000 : ℝ))
      (E := (cell12790 ⟨42, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41313963841323 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (112036287523 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_43 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41296998795003 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (14004560909 / 625000000000 : ℝ))
      (E := (cell12790 ⟨43, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41296998795003 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (14004560909 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_44 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (8256009101361 / 10000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120366876309 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨44, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (8256009101361 / 10000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120366876309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_45 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (82526207924133 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120368885311 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨45, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (82526207924133 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120368885311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_46 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (20623087073099 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560185449467 / 25000000000000 : ℝ))
      (E := (cell12790 ⟨46, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (20623087073099 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560185449467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_47 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (82458512089369 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (224074577363 / 10000000000000 : ℝ))
      (E := (cell12790 ⟨47, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (82458512089369 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (224074577363 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_48 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (20606174821541 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240749813713 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨48, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (20606174821541 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240749813713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_49 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (82390909854041 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240753798021 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨49, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (82390909854041 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240753798021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_50 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (82357143764403 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (280094722879 / 12500000000000 : ℝ))
      (E := (cell12790 ⟨50, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (82357143764403 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (280094722879 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_51 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16464680197759 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240761825107 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨51, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16464680197759 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240761825107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_52 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16457936299781 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (140047862711 / 6250000000000 : ℝ))
      (E := (cell12790 ⟨52, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16457936299781 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (140047862711 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_53 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16451197053313 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120384916407 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨53, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16451197053313 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120384916407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_54 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16444462452749 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (28009673139 / 1250000000000 : ℝ))
      (E := (cell12790 ⟨54, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16444462452749 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (28009673139 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_55 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16437732492511 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240777854801 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨55, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16437732492511 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240777854801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_56 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16431007167049 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120390920077 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨56, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16431007167049 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120390920077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_57 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (82121432354203 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (89631434497 / 4000000000000 : ℝ))
      (E := (cell12790 ⟨57, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (82121432354203 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (89631434497 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_58 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16417570398391 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240789858387 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨58, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16417570398391 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240789858387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_59 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41027147360581 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240793882921 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨59, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41027147360581 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240793882921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12791_40 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (10336981992781 / 12500000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (112029896853 / 5000000000000 : ℝ))
      (E := (cell12791 ⟨40, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (10336981992781 / 12500000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (112029896853 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_41 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (20665469756983 / 25000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240601962477 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨41, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (20665469756983 / 25000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240601962477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_42 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (16525585137709 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448121188823 / 20000000000000 : ℝ))
      (E := (cell12791 ⟨42, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (16525585137709 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448121188823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_43 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (16518799178893 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140038121237 / 6250000000000 : ℝ))
      (E := (cell12791 ⟨43, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (16518799178893 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140038121237 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_44 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (82560089616219 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240613948353 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨44, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (82560089616219 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240613948353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_45 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41263103412241 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240617968427 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨45, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41263103412241 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240617968427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_46 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (3299693899603 / 4000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240621998427 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨46, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (3299693899603 / 4000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240621998427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_47 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (82458511583967 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (70019561801 / 3125000000000 : ℝ))
      (E := (cell12791 ⟨47, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (82458511583967 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (70019561801 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_48 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (3296987963091 / 4000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140039372681 / 6250000000000 : ℝ))
      (E := (cell12791 ⟨48, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (3296987963091 / 4000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140039372681 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_49 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (10298863742657 / 12500000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120317005479 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨49, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (10298863742657 / 12500000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120317005479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_50 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (16471428829463 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120319000731 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨50, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (16471428829463 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120319000731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_51 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41161700833499 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240641990699 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨51, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41161700833499 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240641990699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_52 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (16457936494399 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120323017419 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨52, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (16457936494399 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120323017419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_53 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (16451197306827 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240650012753 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨53, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (16451197306827 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240650012753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_54 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (5138894614087 / 6250000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448130807851 / 20000000000000 : ℝ))
      (E := (cell12791 ⟨54, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (5138894614087 / 6250000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448130807851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_55 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (657509314543 / 800000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (560164512953 / 25000000000000 : ℝ))
      (E := (cell12791 ⟨55, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (657509314543 / 800000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (560164512953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_56 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (16431007596767 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (218814653 / 9765625000 : ℝ))
      (E := (cell12791 ⟨56, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (16431007596767 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (218814653 / 9765625000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_57 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41060717397831 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240666079223 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨57, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41060717397831 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240666079223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_58 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (82087854725881 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140041880381 / 6250000000000 : ℝ))
      (E := (cell12791 ⟨58, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (82087854725881 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140041880381 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_59 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (16410859549431 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240674063017 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨59, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (16410859549431 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240674063017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12792_40 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82695853350637 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240478187051 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨40, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82695853350637 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240478187051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_41 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82661876735671 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240482153069 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨41, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82661876735671 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240482153069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_42 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82627923695221 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (448097238711 / 20000000000000 : ℝ))
      (E := (cell12792 ⟨42, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82627923695221 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (448097238711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_43 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82593994199667 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240490189987 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨43, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82593994199667 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240490189987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_44 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (16512017643907 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240494199991 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨44, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (16512017643907 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240494199991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_45 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (165052411451 / 200000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240498163323 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨45, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (165052411451 / 200000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240498163323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_46 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82492346688387 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560125549029 / 25000000000000 : ℝ))
      (E := (cell12792 ⟨46, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82492346688387 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560125549029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_47 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (20614627769791 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120253089399 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨47, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (20614627769791 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120253089399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_48 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (20606174717237 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (70015944599 / 3125000000000 : ℝ))
      (E := (cell12792 ⟨48, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (20606174717237 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (70015944599 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_49 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41195455014499 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560128555283 / 25000000000000 : ℝ))
      (E := (cell12792 ⟨49, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41195455014499 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560128555283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_50 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41178572265359 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120259108583 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨50, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41178572265359 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120259108583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_51 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82323402345657 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120261106307 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨51, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82323402345657 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120261106307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_52 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (321444075959 / 390625000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240526263647 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨52, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (321444075959 / 390625000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240526263647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_53 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (8225598780209 / 10000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240530249137 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨53, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (8225598780209 / 10000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240530249137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_54 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (20555578846847 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240534224809 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨54, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (20555578846847 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240534224809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_55 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82188666173509 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240538246277 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨55, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82188666173509 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240538246277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_56 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (16431008026541 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (280067781347 / 12500000000000 : ℝ))
      (E := (cell12792 ⟨56, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (16431008026541 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (280067781347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_57 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (16424287447473 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240546293549 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨57, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (16424287447473 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240546293549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_58 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (5130491091251 / 6250000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (224055025219 / 10000000000000 : ℝ))
      (E := (cell12792 ⟨58, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (5130491091251 / 6250000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (224055025219 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_59 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41027150386661 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240554299913 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨59, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41027150386661 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240554299913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12793_40 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (20673962689969 / 25000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240358433951 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨40, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (20673962689969 / 25000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240358433951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_41 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82661874444223 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448072479877 / 20000000000000 : ℝ))
      (E := (cell12793 ⟨41, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82661874444223 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448072479877 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_42 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (3305116868107 / 4000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (89614657599 / 4000000000000 : ℝ))
      (E := (cell12793 ⟨42, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (3305116868107 / 4000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (89614657599 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_43 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (8259399250561 / 10000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240370437201 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨43, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (8259399250561 / 10000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240370437201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_44 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (16512017364711 / 20000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120187224343 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨44, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (16512017364711 / 20000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120187224343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_45 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (20631551156797 / 25000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (280047301773 / 12500000000000 : ℝ))
      (E := (cell12793 ⟨45, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (20631551156797 / 25000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (280047301773 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_46 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82492345887333 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (224038244983 / 10000000000000 : ℝ))
      (E := (cell12793 ⟨46, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82492345887333 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (224038244983 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_47 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82458510574959 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (44807728721 / 2000000000000 : ℝ))
      (E := (cell12793 ⟨47, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82458510574959 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (44807728721 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_48 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82424698661183 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240390488643 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨48, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82424698661183 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240390488643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_49 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82390910117267 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (280049310939 / 12500000000000 : ℝ))
      (E := (cell12793 ⟨49, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82390910117267 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (280049310939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_50 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82357144914613 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448079697827 / 20000000000000 : ℝ))
      (E := (cell12793 ⟨50, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82357144914613 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448079697827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_51 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (20580850756193 / 25000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448080498171 / 20000000000000 : ℝ))
      (E := (cell12793 ⟨51, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (20580850756193 / 25000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448080498171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_52 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41144842209717 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560101622451 / 25000000000000 : ℝ))
      (E := (cell12793 ⟨52, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41144842209717 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560101622451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_53 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (8225598907043 / 10000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (280051310363 / 12500000000000 : ℝ))
      (E := (cell12793 ⟨53, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (8225598907043 / 10000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (280051310363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_54 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41111158474867 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240414525953 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨54, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41111158474867 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240414525953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_55 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41094334014729 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240418497307 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨55, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41094334014729 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240418497307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_56 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41077521140927 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448084502291 / 20000000000000 : ℝ))
      (E := (cell12793 ⟨56, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41077521140927 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448084502291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_57 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (5132589979957 / 6250000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120213252701 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨57, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (5132589979957 / 6250000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120213252701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_58 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (2052196504859 / 2500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448086106841 / 20000000000000 : ℝ))
      (E := (cell12793 ⟨58, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (2052196504859 / 2500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448086106841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_59 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41027151899831 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (224043453441 / 10000000000000 : ℝ))
      (E := (cell12793 ⟨59, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41027151899831 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (224043453441 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12794_40 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82695848169963 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240238677761 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨40, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82695848169963 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240238677761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_41 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (20665468038397 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560060675357 / 25000000000000 : ℝ))
      (E := (cell12794 ⟨41, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (20665468038397 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560060675357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_42 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (16525583942181 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (112012334169 / 5000000000000 : ℝ))
      (E := (cell12794 ⟨42, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (16525583942181 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (112012334169 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_43 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82593990812293 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240250740263 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨43, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82593990812293 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240250740263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_44 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82560085428281 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120127347219 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨44, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82560085428281 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120127347219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_45 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41263101764773 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240258721013 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨45, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41263101764773 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240258721013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_46 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82492345086913 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120131350337 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨46, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82492345086913 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120131350337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_47 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (10307313758919 / 12500000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240266749389 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨47, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (10307313758919 / 12500000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240266749389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_48 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82424698453981 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (56006768683 / 2500000000000 : ℝ))
      (E := (cell12794 ⟨48, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82424698453981 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (56006768683 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_49 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41195455103031 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560068687783 / 25000000000000 : ℝ))
      (E := (cell12794 ⟨49, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41195455103031 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560068687783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_50 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82357145299 / 100000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (112013937919 / 5000000000000 : ℝ))
      (E := (cell12794 ⟨50, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82357145299 / 100000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (112013937919 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_51 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82323403704343 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (280035345801 / 12500000000000 : ℝ))
      (E := (cell12794 ⟨51, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82323403704343 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (280035345801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_52 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (10286210674223 / 12500000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120143386173 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨52, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (10286210674223 / 12500000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120143386173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_53 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (16451198067831 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240290773117 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨53, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (16451198067831 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240290773117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_54 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (8222231851243 / 10000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240294765431 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨54, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (8222231851243 / 10000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240294765431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_55 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82188669885721 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120149402451 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨55, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82188669885721 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120149402451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_56 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41077522215641 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240302828761 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨56, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41077522215641 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240302828761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_57 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82121442121503 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448061366619 / 20000000000000 : ℝ))
      (E := (cell12794 ⟨57, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82121442121503 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448061366619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_58 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82087862928913 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448062162757 / 20000000000000 : ℝ))
      (E := (cell12794 ⟨58, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82087862928913 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448062162757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_59 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (1282098544159 / 1562500000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (224031482571 / 10000000000000 : ℝ))
      (E := (cell12794 ⟨59, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (1282098544159 / 1562500000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (224031482571 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12795_40 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82695845580899 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (560029744309 / 25000000000000 : ℝ))
      (E := (cell12795 ⟨40, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82695845580899 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (560029744309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_41 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41330934931883 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240123000417 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨41, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41330934931883 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240123000417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_42 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (10328489714989 / 12500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (17921016331 / 800000000000 : ℝ))
      (E := (cell12795 ⟨42, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (10328489714989 / 12500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (17921016331 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_43 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82593989119717 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (280016380043 / 12500000000000 : ℝ))
      (E := (cell12795 ⟨43, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82593989119717 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (280016380043 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_44 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (5160005252107 / 6250000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120067527473 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨44, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (5160005252107 / 6250000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120067527473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_45 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82526202432573 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120069512467 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨45, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82526202432573 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120069512467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_46 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41246172143563 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120071533221 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨46, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41246172143563 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120071533221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_47 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82458509568343 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120073529947 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨47, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82458509568343 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120073529947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_48 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82424698247341 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (17501180173 / 781250000000 : ℝ))
      (E := (cell12795 ⟨48, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82424698247341 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (17501180173 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_49 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (10298863786923 / 12500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120077535479 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨49, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (10298863786923 / 12500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120077535479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_50 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82357145683877 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (560039770973 / 25000000000000 : ℝ))
      (E := (cell12795 ⟨50, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82357145683877 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (560039770973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_51 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82323404384369 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (140010193643 / 6250000000000 : ℝ))
      (E := (cell12795 ⟨51, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82323404384369 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (140010193643 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_52 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41144843184277 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (560041777819 / 25000000000000 : ℝ))
      (E := (cell12795 ⟨52, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41144843184277 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (560041777819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_53 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (16451198321653 / 20000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120085530357 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨53, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (16451198321653 / 20000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120085530357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_54 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (3288892803019 / 4000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240175120501 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨54, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (3288892803019 / 4000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240175120501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_55 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41094335871149 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120089554977 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨55, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41094335871149 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120089554977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_56 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82155046580989 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120091542213 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨56, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82155046580989 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120091542213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_57 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41060722281969 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240187099161 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨57, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41060722281969 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240187099161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_58 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41043932831837 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240191150109 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨58, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41043932831837 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240191150109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_59 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (1282098591451 / 1562500000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240195114609 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨59, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (1282098591451 / 1562500000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240195114609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12796_40 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82695842992683 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239999332379 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨40, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82695842992683 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239999332379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_41 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (20665466893689 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1120001677567 / 50000000000000 : ℝ))
      (E := (cell12796 ⟨41, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (20665466893689 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1120001677567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_42 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (16525583145939 / 20000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240007337551 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨42, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (16525583145939 / 20000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240007337551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_43 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (41296993713941 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240011337447 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨43, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (41296993713941 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240011337447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_44 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82560082639847 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240015353663 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨44, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82560082639847 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240015353663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_45 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (20631550334067 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (89600775393 / 4000000000000 : ℝ))
      (E := (cell12796 ⟨45, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (20631550334067 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (89600775393 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_46 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (20623085871993 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (448004674089 / 20000000000000 : ℝ))
      (E := (cell12796 ⟨46, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (20623085871993 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (448004674089 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_47 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82458509065931 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240027367567 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨47, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82458509065931 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240027367567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_48 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82424698041263 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (560007843543 / 25000000000000 : ℝ))
      (E := (cell12796 ⟨48, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82424698041263 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (560007843543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_49 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (5149431899077 / 6250000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1120017694013 / 50000000000000 : ℝ))
      (E := (cell12796 ⟨49, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (5149431899077 / 6250000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1120017694013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_50 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (20589286517311 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1120019703341 / 50000000000000 : ℝ))
      (E := (cell12796 ⟨50, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (20589286517311 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1120019703341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_51 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82323405064851 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240043427481 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨51, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82323405064851 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240043427481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_52 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (642888182373 / 781250000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (448009489511 / 20000000000000 : ℝ))
      (E := (cell12796 ⟨52, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (642888182373 / 781250000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (448009489511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_53 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82255992877759 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (56001285119 / 2500000000000 : ℝ))
      (E := (cell12796 ⟨53, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82255992877759 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (56001285119 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_54 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82222321638869 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240055413909 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨54, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82222321638869 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240055413909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_55 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82188673599189 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240059471573 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨55, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82188673599189 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240059471573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_56 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (41077524365487 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (44801269117 / 2000000000000 : ℝ))
      (E := (cell12796 ⟨56, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (41077524365487 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (44801269117 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_57 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (10265180875827 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240067481069 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨57, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (10265180875827 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240067481069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_58 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (20521967099661 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240071483999 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨58, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (20521967099661 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2240071483999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_59 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (20513578219931 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (560018865079 / 25000000000000 : ℝ))
      (E := (cell12796 ⟨59, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (20513578219931 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (560018865079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12797_40 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (16539168081063 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239879743191 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨40, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (16539168081063 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239879743191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_41 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41330932643279 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (5599709267 / 250000000000 : ℝ))
      (E := (cell12797 ⟨41, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41330932643279 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (5599709267 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_42 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (16525582748051 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239887748319 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨42, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (16525582748051 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239887748319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_43 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82593985736787 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119945874613 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨43, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82593985736787 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119945874613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_44 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82560081246687 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239895767139 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨44, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82560081246687 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239895767139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_45 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (10315775030079 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559974935453 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨45, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (10315775030079 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559974935453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_46 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82492342689451 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239903730477 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨46, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82492342689451 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239903730477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_47 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (20614627141029 / 25000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559976947563 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨47, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (20614627141029 / 25000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559976947563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_48 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41212348917873 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239911742351 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨48, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41212348917873 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239911742351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_49 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41195455237803 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239915761303 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨49, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41195455237803 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239915761303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_50 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82357146455103 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111995989287 / 5000000000000 : ℝ))
      (E := (cell12797 ⟨50, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82357146455103 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111995989287 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_51 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (20580851436447 / 25000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239923813003 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨51, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (20580851436447 / 25000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239923813003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_52 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41144844159677 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (34998871581 / 1562500000000 : ℝ))
      (E := (cell12797 ⟨52, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41144844159677 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (34998871581 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_53 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82255994147637 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119965902627 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨53, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82255994147637 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119965902627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_54 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (20555580800653 / 25000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239935822909 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨54, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (20555580800653 / 25000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239935822909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_55 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41094337728197 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (44798796613 / 2000000000000 : ℝ))
      (E := (cell12797 ⟨55, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41094337728197 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (44798796613 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_56 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41077525440619 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (223994382477 / 10000000000000 : ℝ))
      (E := (cell12797 ⟨56, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41077525440619 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (223994382477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_57 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41060724724769 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559986965127 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨57, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41060724724769 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559986965127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_58 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41043935566911 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239951815457 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨58, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41043935566911 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239951815457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_59 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82054315906759 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119977931413 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨59, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82054315906759 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119977931413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12798_40 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (16539167563759 / 20000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (447952030183 / 20000000000000 : ℝ))
      (E := (cell12798 ⟨40, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (16539167563759 / 20000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (447952030183 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_41 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (20665465749793 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (447952822839 / 20000000000000 : ℝ))
      (E := (cell12798 ⟨41, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (20665465749793 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (447952822839 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_42 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (8262791175159 / 10000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119884078037 / 50000000000000 : ℝ))
      (E := (cell12798 ⟨42, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (8262791175159 / 10000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119884078037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_43 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (2581062001451 / 3125000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559943039507 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨43, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (2581062001451 / 3125000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559943039507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_44 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (8256007985423 / 10000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (89591044753 / 4000000000000 : ℝ))
      (E := (cell12798 ⟨44, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (8256007985423 / 10000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (89591044753 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_45 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (16505239829133 / 20000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (139986259673 / 6250000000000 : ℝ))
      (E := (cell12798 ⟨45, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (16505239829133 / 20000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (139986259673 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_46 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82492341891563 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (111989207327 / 5000000000000 : ℝ))
      (E := (cell12798 ⟨46, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82492341891563 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (111989207327 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_47 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (41229254031449 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (139986759449 / 6250000000000 : ℝ))
      (E := (cell12798 ⟨47, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (41229254031449 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (139986759449 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_48 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82424697630791 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239792166679 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨48, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82424697630791 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239792166679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_49 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (41195455283253 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (223979619079 / 10000000000000 : ℝ))
      (E := (cell12798 ⟨49, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (41195455283253 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (223979619079 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_50 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (20589286710363 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239800162077 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨50, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (20589286710363 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239800162077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_51 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82323406427179 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239804195841 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨51, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82323406427179 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239804195841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_52 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82289689295383 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239808171203 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨52, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82289689295383 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239808171203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_53 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (822559954179 / 1000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (447962440627 / 20000000000000 : ℝ))
      (E := (cell12798 ⟨53, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (822559954179 / 1000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (447962440627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_54 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (5138895297919 / 6250000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239816229333 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨54, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (5138895297919 / 6250000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239816229333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_55 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82188677313913 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (279977530787 / 12500000000000 : ℝ))
      (E := (cell12798 ⟨55, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82188677313913 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (279977530787 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_56 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82155053031781 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559956062579 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨56, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82155053031781 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559956062579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_57 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82121451892703 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119914118739 / 50000000000000 : ℝ))
      (E := (cell12798 ⟨57, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82121451892703 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119914118739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_58 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (10260984233651 / 12500000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (55995806571 / 2500000000000 : ℝ))
      (E := (cell12798 ⟨58, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (10260984233651 / 12500000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (55995806571 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_59 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (41027159466983 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (111991813147 / 5000000000000 : ℝ))
      (E := (cell12798 ⟨59, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (41027159466983 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (111991813147 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12799_40 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82695835233123 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239640555553 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨40, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82695835233123 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239640555553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_41 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82661860712597 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239644577321 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨41, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82661860712597 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239644577321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_42 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82627909763701 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (139978035051 / 6250000000000 : ℝ))
      (E := (cell12799 ⟨42, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82627909763701 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (139978035051 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_43 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82593982356817 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239652563853 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨43, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82593982356817 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239652563853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_44 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41280039231239 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (279957073159 / 12500000000000 : ℝ))
      (E := (cell12799 ⟨44, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41280039231239 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (279957073159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_45 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41263099025683 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239660564821 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨45, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41263099025683 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239660564821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_46 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82492341094307 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119832309317 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨46, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82492341094307 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119832309317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_47 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82458507562277 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (139979285513 / 6250000000000 : ℝ))
      (E := (cell12799 ⟨47, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82458507562277 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (139979285513 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_48 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82424697426397 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (447934517643 / 20000000000000 : ℝ))
      (E := (cell12799 ⟨48, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82424697426397 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (447934517643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_49 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (20597727664483 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (27995957719 / 1250000000000 : ℝ))
      (E := (cell12799 ⟨49, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (20597727664483 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (27995957719 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_50 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82357147228291 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (559920148671 / 25000000000000 : ℝ))
      (E := (cell12799 ⟨50, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82357147228291 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (559920148671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_51 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41161703554513 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (17497536211 / 781250000000 : ℝ))
      (E := (cell12799 ⟨51, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41161703554513 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (17497536211 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_52 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (10286211283979 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (559922154403 / 25000000000000 : ℝ))
      (E := (cell12799 ⟨52, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (10286211283979 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (559922154403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_53 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41127998344273 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239692657467 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨53, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41127998344273 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239692657467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_54 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (16444465266229 / 20000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239696633181 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨54, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (16444465266229 / 20000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239696633181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_55 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (16437735834349 / 20000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119850329701 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨55, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (16437735834349 / 20000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119850329701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_56 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41077527591301 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239704673359 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨56, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41077527591301 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239704673359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_57 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82121454336111 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (69990895973 / 3125000000000 : ℝ))
      (E := (cell12799 ⟨57, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82121454336111 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (69990895973 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_58 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82087876604803 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239712648611 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨58, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82087876604803 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239712648611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_59 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82054321961347 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239716660657 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨59, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82054321961347 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239716660657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

end BstLean.Part268
