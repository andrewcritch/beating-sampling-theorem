import BstLean.Part268CellShard17Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12775_20 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41690265410781 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242438428957 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨20, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41690265410781 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242438428957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_21 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (20836517755159 / 25000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242442423607 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨21, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (20836517755159 / 25000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242442423607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_22 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (83311635426719 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242446451933 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨22, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (83311635426719 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242446451933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_23 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41638612003497 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121225229631 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨23, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41638612003497 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121225229631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_24 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (83242836728811 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (140153403061 / 6250000000000 : ℝ))
      (E := (cell12775 ⟨24, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (83242836728811 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (140153403061 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_25 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (8320847355969 / 10000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242458482619 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨25, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (8320847355969 / 10000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242458482619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_26 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (16634826893463 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121231223161 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨26, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (16634826893463 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121231223161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_27 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (5196238713721 / 6250000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242466459591 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨27, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (5196238713721 / 6250000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242466459591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_28 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (83105528384369 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242470466467 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨28, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (83105528384369 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242470466467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_29 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (10383907666249 / 12500000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448494893833 / 20000000000000 : ℝ))
      (E := (cell12775 ⟨29, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (10383907666249 / 12500000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448494893833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_30 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41518509112373 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242478469669 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨30, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41518509112373 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242478469669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_31 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41501399518567 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242482469733 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨31, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41501399518567 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242482469733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_32 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41484301867909 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242486470883 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨32, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41484301867909 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242486470883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_33 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (4146721614481 / 5000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242490474421 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨33, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (4146721614481 / 5000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242490474421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_34 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82900284667523 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (280311810177 / 12500000000000 : ℝ))
      (E := (cell12775 ⟨34, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82900284667523 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (280311810177 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_35 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82866160838663 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121249246359 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨35, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82866160838663 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121249246359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_36 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82832060772337 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242502508947 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨36, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82832060772337 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242502508947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_37 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (16559596887599 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (280313316313 / 12500000000000 : ℝ))
      (E := (cell12775 ⟨37, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (16559596887599 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (280313316313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_38 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82763931805243 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448502099771 / 20000000000000 : ℝ))
      (E := (cell12775 ⟨38, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82763931805243 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448502099771 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_39 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (82729902843839 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560628632837 / 25000000000000 : ℝ))
      (E := (cell12775 ⟨39, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (82729902843839 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560628632837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12776_20 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41690261064867 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448463639859 / 20000000000000 : ℝ))
      (E := (cell12776 ⟨20, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41690261064867 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448463639859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_21 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83346062637173 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242322178501 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨21, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83346062637173 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242322178501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_22 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83311627351191 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242326192087 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨22, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83311627351191 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242326192087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_23 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (20819304059743 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121165092691 / 50000000000000 : ℝ))
      (E := (cell12776 ⟨23, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (20819304059743 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121165092691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_24 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (20810707316967 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560583540441 / 25000000000000 : ℝ))
      (E := (cell12776 ⟨24, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (20810707316967 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560583540441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_25 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83208466405397 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242338182781 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨25, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83208466405397 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242338182781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_26 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41587063809623 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (280292774123 / 12500000000000 : ℝ))
      (E := (cell12776 ⟨26, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41587063809623 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (280292774123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_27 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83139812877267 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242346195049 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨27, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83139812877267 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242346195049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_28 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41552761073737 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (35036721741 / 1562500000000 : ℝ))
      (E := (cell12776 ⟨28, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41552761073737 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (35036721741 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_29 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (2595976731189 / 3125000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242354184319 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨29, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (2595976731189 / 3125000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242354184319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_30 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83037012597329 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (3503684741 / 156250000000 : ℝ))
      (E := (cell12776 ⟨30, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83037012597329 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (3503684741 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_31 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41501396856911 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242362225921 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨31, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41501396856911 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242362225921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_32 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (8296859871619 / 10000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242366219387 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨32, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (8296859871619 / 10000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242366219387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_33 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (10366803446657 / 12500000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121185107967 / 50000000000000 : ℝ))
      (E := (cell12776 ⟨33, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (10366803446657 / 12500000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121185107967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_34 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (82900280254003 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448474843327 / 20000000000000 : ℝ))
      (E := (cell12776 ⟨34, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (82900280254003 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448474843327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_35 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (5179134795473 / 6250000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242378222337 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨35, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (5179134795473 / 6250000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242378222337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_36 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (5177003560203 / 6250000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121191116831 / 50000000000000 : ℝ))
      (E := (cell12776 ⟨36, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (5177003560203 / 6250000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121191116831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_37 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (16559596186099 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242386251007 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨37, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (16559596186099 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242386251007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_38 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (16552785719783 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242390215839 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨38, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (16552785719783 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242390215839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_39 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (20682474984567 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (17518705043 / 781250000000 : ℝ))
      (E := (cell12776 ⟨39, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (20682474984567 / 25000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (17518705043 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12777_20 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41690256719747 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242197965773 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨20, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41690256719747 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242197965773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_21 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (4167302712763 / 5000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121100964787 / 50000000000000 : ℝ))
      (E := (cell12777 ⟨21, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (4167302712763 / 5000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121100964787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_22 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (10413952409647 / 12500000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (112110296423 / 5000000000000 : ℝ))
      (E := (cell12777 ⟨22, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (10413952409647 / 12500000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (112110296423 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_23 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41638604236213 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (448441993223 / 20000000000000 : ℝ))
      (E := (cell12777 ⟨23, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41638604236213 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (448441993223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_24 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41621410904181 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560553482307 / 25000000000000 : ℝ))
      (E := (cell12777 ⟨24, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41621410904181 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560553482307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_25 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41604229626253 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560554484419 / 25000000000000 : ℝ))
      (E := (cell12777 ⟨25, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41604229626253 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560554484419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_26 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (83174120772543 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121110968007 / 50000000000000 : ℝ))
      (E := (cell12777 ⟨26, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (83174120772543 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121110968007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_27 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (3325592253453 / 4000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121112992683 / 50000000000000 : ℝ))
      (E := (cell12777 ⟨27, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (3325592253453 / 4000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121112992683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_28 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (8310551591187 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (22422299713 / 1000000000000 : ℝ))
      (E := (cell12777 ⟨28, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (8310551591187 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (22422299713 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_29 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41535624733679 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242233954453 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨29, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41535624733679 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242233954453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_30 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (8303700697113 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242237995331 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨30, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (8303700697113 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242237995331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_31 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (20750697097923 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242241978667 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨31, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (20750697097923 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242241978667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_32 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82968593697707 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560561491121 / 25000000000000 : ℝ))
      (E := (cell12777 ⟨32, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82968593697707 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560561491121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_33 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41467211429 / 50000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242250012671 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨33, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41467211429 / 50000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242250012671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_34 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82900275841553 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (112112700357 / 5000000000000 : ℝ))
      (E := (cell12777 ⟨34, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82900275841553 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (112112700357 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_35 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82866152617507 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242258007303 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨35, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82866152617507 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242258007303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_36 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82832053155157 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242262013783 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨36, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82832053155157 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242262013783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_37 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82797977423957 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (70070813343 / 3125000000000 : ℝ))
      (E := (cell12777 ⟨37, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82797977423957 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (70070813343 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_38 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (82763925393513 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (44845399767 / 2000000000000 : ℝ))
      (E := (cell12777 ⟨38, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (82763925393513 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (44845399767 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_39 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41364948516793 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (140142125953 / 6250000000000 : ℝ))
      (E := (cell12777 ⟨39, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41364948516793 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (140142125953 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12778_20 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (2084512618771 / 2500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560519432099 / 25000000000000 : ℝ))
      (E := (cell12778 ⟨20, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (2084512618771 / 2500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560519432099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_21 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (5209127867181 / 6250000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242081735139 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨21, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (5209127867181 / 6250000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242081735139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_22 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83311611204673 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121042859693 / 50000000000000 : ℝ))
      (E := (cell12778 ⟨22, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83311611204673 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121042859693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_23 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (16655440141471 / 20000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121044871553 / 50000000000000 : ℝ))
      (E := (cell12778 ⟨23, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (16655440141471 / 20000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121044871553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_24 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (16648562870059 / 20000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242093751367 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨24, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (16648562870059 / 20000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242093751367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_25 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (10401056512627 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242097747309 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨25, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (10401056512627 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242097747309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_26 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83174113927203 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560525433461 / 25000000000000 : ℝ))
      (E := (cell12778 ⟨26, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83174113927203 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560525433461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_27 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83139799796711 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242105772093 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨27, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83139799796711 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242105772093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_28 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83105509677557 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242109747623 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨28, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83105509677557 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242109747623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_29 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83071243537921 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (224211377957 / 10000000000000 : ℝ))
      (E := (cell12778 ⟨29, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83071243537921 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (224211377957 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_30 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (20759250336537 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448423550589 / 20000000000000 : ℝ))
      (E := (cell12778 ⟨30, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (20759250336537 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448423550589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_31 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (41501391535371 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242121786517 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨31, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (41501391535371 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242121786517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_32 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (5185536792523 / 6250000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242125764747 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨32, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (5185536792523 / 6250000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242125764747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_33 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82934418143851 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242129806043 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨33, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82934418143851 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242129806043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_34 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (3316010857207 / 4000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560533448579 / 25000000000000 : ℝ))
      (E := (cell12778 ⟨34, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (3316010857207 / 4000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560533448579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_35 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (258956714089 / 312500000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242137788979 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨35, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (258956714089 / 312500000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242137788979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_36 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (2588501542127 / 3125000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560535447663 / 25000000000000 : ℝ))
      (E := (cell12778 ⟨36, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (2588501542127 / 3125000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560535447663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_37 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (4139898695919 / 5000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242145799731 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨37, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (4139898695919 / 5000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242145799731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_38 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (20690980547259 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242149816391 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨38, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (20690980547259 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242149816391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_39 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (82729894129793 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242153781851 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨39, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (82729894129793 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242153781851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12779_20 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (83380496063773 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (44839150909 / 2000000000000 : ℝ))
      (E := (cell12779 ⟨20, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (83380496063773 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (44839150909 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_21 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41673018748041 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241961536887 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨21, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41673018748041 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241961536887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_22 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41655801566841 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120982782433 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨22, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41655801566841 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120982782433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_23 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (83277192943759 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (280246196839 / 12500000000000 : ℝ))
      (E := (cell12779 ⟨23, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (83277192943759 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (280246196839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_24 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41621403446833 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241973569803 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨24, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41621403446833 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241973569803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_25 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41604222475463 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241977553279 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨25, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41604222475463 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241977553279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_26 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (20793526770807 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (280247698309 / 12500000000000 : ℝ))
      (E := (cell12779 ⟨26, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (20793526770807 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (280247698309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_27 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (10392474157303 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241985555229 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨27, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (10392474157303 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241985555229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_28 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41552751722267 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241989578867 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨28, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41552751722267 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241989578867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_29 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41535618804869 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241993601173 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨29, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41535618804869 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241993601173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_30 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41518497861191 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560499391401 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨30, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41518497861191 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560499391401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_31 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (83002777750971 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (224200159093 / 10000000000000 : ℝ))
      (E := (cell12779 ⟨31, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (83002777750971 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (224200159093 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_32 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (20742145916043 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242005620177 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨32, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (20742145916043 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242005620177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_33 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82934413430809 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242009596051 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨33, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82934413430809 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242009596051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_34 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82900267019867 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (112100681839 / 5000000000000 : ℝ))
      (E := (cell12779 ⟨34, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82900267019867 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (112100681839 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_35 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82866144400487 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242017626003 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨35, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82866144400487 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242017626003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_36 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (5177002846373 / 6250000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (224202162293 / 10000000000000 : ℝ))
      (E := (cell12779 ⟨36, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (5177002846373 / 6250000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (224202162293 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_37 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (20699492603441 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560506406989 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨37, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (20699492603441 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560506406989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_38 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (20690979746371 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121014820627 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨38, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (20690979746371 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1121014820627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_39 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (82729891226889 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242033662777 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨39, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (82729891226889 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2242033662777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12780_20 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83380487378291 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448367483387 / 20000000000000 : ℝ))
      (E := (cell12780 ⟨20, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83380487378291 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448367483387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_21 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (2604563409963 / 3125000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (280230174141 / 12500000000000 : ℝ))
      (E := (cell12780 ⟨21, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (2604563409963 / 3125000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (280230174141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_22 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83311595064203 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241845406567 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨22, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83311595064203 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241845406567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_23 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83277185181637 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120924701289 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨23, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83277185181637 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120924701289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_24 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41621399719237 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241853442917 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨24, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41621399719237 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241853442917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_25 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41604218901119 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448371482797 / 20000000000000 : ℝ))
      (E := (cell12780 ⟨25, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41604218901119 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448371482797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_26 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (10396762530077 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120930717737 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨26, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (10396762530077 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120930717737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_27 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (10392473340183 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241865451677 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨27, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (10392473340183 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241865451677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_28 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (25970467879 / 31250000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (560467366259 / 25000000000000 : ℝ))
      (E := (cell12780 ⟨28, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (25970467879 / 31250000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (560467366259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_29 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (10383903960351 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120936709631 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨29, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (10383903960351 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120936709631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_30 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83036990099833 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120938716653 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨30, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83036990099833 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120938716653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_31 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83002772432381 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120940725223 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨31, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83002772432381 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120940725223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_32 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82968578649119 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448377094441 / 20000000000000 : ℝ))
      (E := (cell12780 ⟨32, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82968578649119 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448377094441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_33 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82934408718873 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241889441287 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨33, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82934408718873 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241889441287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_34 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82900262610629 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120946737959 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨34, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82900262610629 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120946737959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_35 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (10358267536691 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120948729869 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨35, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (10358267536691 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120948729869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_36 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (8283204173687 / 10000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (560475362989 / 25000000000000 : ℝ))
      (E := (cell12780 ⟨36, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (8283204173687 / 10000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (560475362989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_37 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (8279796691011 / 10000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (44838110233 / 2000000000000 : ℝ))
      (E := (cell12780 ⟨37, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (8279796691011 / 10000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (44838110233 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_38 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (10345489472857 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241909462941 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨38, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (10345489472857 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241909462941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_39 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (82729888324873 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241913481831 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨39, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (82729888324873 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241913481831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12781_20 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (16676095738879 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241717284567 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨20, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (16676095738879 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241717284567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_21 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83346020743099 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241721303863 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨21, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83346020743099 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241721303863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_22 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (41655793498117 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (89669012113 / 4000000000000 : ℝ))
      (E := (cell12781 ⟨22, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (41655793498117 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (89669012113 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_23 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83277177420989 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120864642531 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨23, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83277177420989 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120864642531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_24 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (1040534899809 / 1250000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (280216664041 / 12500000000000 : ℝ))
      (E := (cell12781 ⟨24, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (1040534899809 / 1250000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (280216664041 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_25 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83208430654949 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (280217166179 / 12500000000000 : ℝ))
      (E := (cell12781 ⟨25, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83208430654949 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (280217166179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_26 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83174093399367 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120870669639 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨26, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83174093399367 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120870669639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_27 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83139780185829 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120872672269 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨27, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83139780185829 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120872672269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_28 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (20776372745589 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241749347653 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨28, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (20776372745589 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241749347653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_29 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83071225757131 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140109584427 / 6250000000000 : ℝ))
      (E := (cell12781 ⟨29, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83071225757131 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140109584427 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_30 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (166073968957 / 200000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (448351471211 / 20000000000000 : ℝ))
      (E := (cell12781 ⟨30, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (166073968957 / 200000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (448351471211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_31 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (8300276711497 / 10000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (224176136507 / 10000000000000 : ℝ))
      (E := (cell12781 ⟨31, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (8300276711497 / 10000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (224176136507 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_32 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82968573635209 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120882660417 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨32, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82968573635209 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120882660417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_33 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (20733601002011 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241769341751 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨33, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (20733601002011 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241769341751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_34 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (4145012910123 / 5000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241773370347 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨34, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (4145012910123 / 5000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241773370347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_35 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (41433068093801 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (280222168603 / 12500000000000 : ℝ))
      (E := (cell12781 ⟨35, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (41433068093801 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (280222168603 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_36 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82832037932769 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241781336393 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨36, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82832037932769 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241781336393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_37 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (10349745425927 / 12500000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560446348033 / 25000000000000 : ℝ))
      (E := (cell12781 ⟨37, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (10349745425927 / 12500000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560446348033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_38 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (82763912581153 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560447349717 / 25000000000000 : ℝ))
      (E := (cell12781 ⟨38, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (82763912581153 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560447349717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_39 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (16545977084749 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120896678239 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨39, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (16545977084749 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120896678239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12782_20 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (20845117503021 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241597206633 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨20, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (20845117503021 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241597206633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_21 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83346012368929 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448320242157 / 20000000000000 : ℝ))
      (E := (cell12782 ⟨21, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83346012368929 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448320242157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_22 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83311578929777 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241605253639 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨22, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83311578929777 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241605253639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_23 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (10409646207727 / 12500000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241609222163 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨23, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (10409646207727 / 12500000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241609222163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_24 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41621392266201 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (112080661821 / 5000000000000 : ℝ))
      (E := (cell12782 ⟨24, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41621392266201 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (112080661821 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_25 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (4160421175453 / 5000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241617241217 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨25, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (4160421175453 / 5000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241617241217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_26 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83174086559481 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (70050663733 / 3125000000000 : ℝ))
      (E := (cell12782 ⟨26, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83174086559481 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (70050663733 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_27 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83139773651521 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560406308453 / 25000000000000 : ℝ))
      (E := (cell12782 ⟨27, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83139773651521 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560406308453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_28 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41552742376601 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241629226721 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨28, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41552742376601 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241629226721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_29 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83071219832707 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241633278891 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨29, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83071219832707 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241633278891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_30 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83036978858383 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241637275329 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨30, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83036978858383 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241637275329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_31 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41501380899369 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120820638129 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨31, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41501380899369 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120820638129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_32 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (82968568622441 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241645283199 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨32, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (82968568622441 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241645283199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_33 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (1036679991229 / 1250000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448329859489 / 20000000000000 : ℝ))
      (E := (cell12782 ⟨33, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (1036679991229 / 1250000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448329859489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_34 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41450126897681 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241653261449 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨34, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41450126897681 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241653261449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_35 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (8286613208271 / 10000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (112082864663 / 5000000000000 : ℝ))
      (E := (cell12782 ⟨35, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (8286613208271 / 10000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (112082864663 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_36 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (323562633319 / 390625000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120830638121 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨36, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (323562633319 / 390625000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120830638121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_37 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41398979952841 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120832634701 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨37, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41398979952841 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120832634701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_38 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (662111275043 / 800000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (224166927291 / 10000000000000 : ℝ))
      (E := (cell12782 ⟨38, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (662111275043 / 800000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (224166927291 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_39 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41364941261753 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120836643359 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨39, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41364941261753 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120836643359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12783_20 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83380461331357 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (448295436627 / 20000000000000 : ℝ))
      (E := (cell12783 ⟨20, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83380461331357 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (448295436627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_21 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83346003996307 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241481172203 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨21, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83346003996307 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241481172203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_22 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (8331157086483 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120742600339 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨22, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (8331157086483 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120742600339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_23 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (16655432380823 / 20000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (280186144441 / 12500000000000 : ℝ))
      (E := (cell12783 ⟨23, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (16655432380823 / 20000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (280186144441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_24 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (1040534713519 / 1250000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241493156813 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨24, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (1040534713519 / 1250000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241493156813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_25 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (8320841636457 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (35023393871 / 1562500000000 : ℝ))
      (E := (cell12783 ⟨25, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (8320841636457 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (35023393871 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_26 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83174079720957 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241501194439 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨26, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83174079720957 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241501194439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_27 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83139767118539 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241505177949 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨27, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83139767118539 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241505177949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_28 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (10388184815667 / 12500000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241509219189 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨28, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (10388184815667 / 12500000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241509219189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_29 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41535606954767 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (28018915043 / 1250000000000 : ℝ))
      (E := (cell12783 ⟨29, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41535606954767 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (28018915043 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_30 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83036973239481 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241517191131 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨30, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83036973239481 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241517191131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_31 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (16600551296737 / 20000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (224152118401 / 10000000000000 : ℝ))
      (E := (cell12783 ⟨31, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (16600551296737 / 20000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (224152118401 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_32 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (1296383806419 / 1562500000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120762621083 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨32, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (1296383806419 / 1562500000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120762621083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_33 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82934394589703 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241529191187 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨33, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82934394589703 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241529191187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_34 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (20725062347333 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (448306641569 / 20000000000000 : ℝ))
      (E := (cell12783 ⟨34, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (20725062347333 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (448306641569 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_35 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (1657322559577 / 2000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241537234411 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨35, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (1657322559577 / 2000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241537234411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_36 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (20708007581889 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120770606421 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨36, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (20708007581889 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120770606421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_37 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (82797956404909 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241545260829 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨37, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (82797956404909 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241545260829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_38 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (2069097654513 / 2500000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (560387315299 / 25000000000000 : ℝ))
      (E := (cell12783 ⟨38, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (2069097654513 / 2500000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (560387315299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_39 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41364939812077 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241553272553 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨39, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41364939812077 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241553272553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12784_20 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (16676090530443 / 20000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241357155787 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨20, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (16676090530443 / 20000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241357155787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_21 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (5209124726577 / 6250000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241361129809 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨21, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (5209124726577 / 6250000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241361129809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_22 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83311562801393 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (280170642993 / 12500000000000 : ℝ))
      (E := (cell12784 ⟨22, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83311562801393 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (280170642993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_23 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83277154147887 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120684571757 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨23, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83277154147887 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120684571757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_24 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41621384816037 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241373190269 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨24, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41621384816037 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241373190269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_25 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83208409221479 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560344292653 / 25000000000000 : ℝ))
      (E := (cell12784 ⟨25, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83208409221479 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560344292653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_26 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (20793518220949 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241381145799 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨26, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (20793518220949 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241381145799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_27 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83139760586881 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (448277035391 / 20000000000000 : ℝ))
      (E := (cell12784 ⟨27, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83139760586881 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (448277035391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_28 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41552736149379 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241389149637 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨28, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41552736149379 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241389149637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_29 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83071207987613 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241393182977 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨29, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83071207987613 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241393182977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_30 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41518483810897 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120698580991 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨30, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41518483810897 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120698580991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_31 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (8300275116981 / 10000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241401205417 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨31, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (8300275116981 / 10000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241401205417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_32 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (82968558600333 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (280175649717 / 12500000000000 : ℝ))
      (E := (cell12784 ⟨32, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (82968558600333 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (280175649717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_33 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (8293438988219 / 10000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241409198753 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨33, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (8293438988219 / 10000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241409198753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_34 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (20725061246093 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560353302383 / 25000000000000 : ℝ))
      (E := (cell12784 ⟨34, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (20725061246093 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560353302383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_35 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41433061938011 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560354307729 / 25000000000000 : ℝ))
      (E := (cell12784 ⟨35, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41433061938011 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560354307729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_36 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (20708006631611 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241421204857 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨36, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (20708006631611 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241421204857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_37 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (10349744113137 / 12500000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241425190361 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨37, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (10349744113137 / 12500000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241425190361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_38 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (82763902981589 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241429246309 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨38, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (82763902981589 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241429246309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_39 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (82729876725689 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241433255253 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨39, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (82729876725689 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241433255253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12785_20 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83380443974657 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (17929897463 / 800000000000 : ℝ))
      (E := (cell12785 ⟨20, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83380443974657 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (17929897463 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_21 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (10418248406963 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120620570957 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨21, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (10418248406963 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120620570957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_22 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (16662310947893 / 20000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (224124514177 / 10000000000000 : ℝ))
      (E := (cell12785 ⟨22, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (16662310947893 / 20000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (224124514177 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_23 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (20819286598283 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241249186121 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨23, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (20819286598283 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241249186121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_24 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (650334079563 / 781250000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241253161647 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨24, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (650334079563 / 781250000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241253161647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_25 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83208402079787 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120628594111 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨25, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83208402079787 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120628594111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_26 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (20793516511999 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560315287991 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨26, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (20793516511999 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560315287991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_27 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83139754056549 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120632586187 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨27, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83139754056549 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120632586187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_28 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83105466073469 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448253838697 / 20000000000000 : ℝ))
      (E := (cell12785 ⟨28, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83105466073469 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448253838697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_29 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (162248441537 / 195312500000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120636608751 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨29, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (162248441537 / 195312500000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120636608751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_30 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41518481002661 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120638593941 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨30, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41518481002661 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120638593941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_31 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41501372928557 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241281223389 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨31, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41501372928557 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241281223389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_32 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82968553590991 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241285208477 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨32, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82968553590991 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241285208477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_33 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82934385175783 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241289202959 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨33, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82934385175783 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241289202959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_34 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (129531625907 / 156250000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120646603949 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨34, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (129531625907 / 156250000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120646603949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_35 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82866119774227 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (280162153017 / 12500000000000 : ℝ))
      (E := (cell12785 ⟨35, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82866119774227 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (280162153017 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_36 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (10354002840791 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (280162649203 / 12500000000000 : ℝ))
      (E := (cell12785 ⟨36, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (10354002840791 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (280162649203 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_37 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41398974703121 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120652617027 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨37, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41398974703121 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120652617027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_38 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (82763899783581 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (280163653531 / 12500000000000 : ℝ))
      (E := (cell12785 ⟨38, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (82763899783581 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (280163653531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_39 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (5170617114257 / 6250000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448262646963 / 20000000000000 : ℝ))
      (E := (cell12785 ⟨39, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (5170617114257 / 6250000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448262646963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12786_20 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41690217649341 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241117206117 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨20, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41690217649341 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241117206117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_21 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41672989443861 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241121208519 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨21, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41672989443861 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241121208519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_22 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83311546679047 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241125194157 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨22, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83311546679047 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241125194157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_23 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83277138639849 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120564612497 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨23, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83277138639849 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120564612497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_24 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83242754737489 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241133187709 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨24, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83242754737489 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241133187709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_25 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83208394939493 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2188610549 / 97656250000 : ℝ))
      (E := (cell12786 ⟨25, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83208394939493 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2188610549 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_26 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83174059213557 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120570606469 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨26, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83174059213557 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120570606469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_27 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83139747527541 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241145222663 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨27, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83139747527541 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241145222663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_28 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (20776364962367 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241149233789 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨28, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (20776364962367 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241149233789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_29 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (3322847845901 / 4000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120576624261 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨29, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (3322847845901 / 4000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120576624261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_30 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (5189809774379 / 6250000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241157210313 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨30, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (5189809774379 / 6250000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241157210313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_31 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (16600548109119 / 20000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (224116123793 / 10000000000000 : ℝ))
      (E := (cell12786 ⟨31, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (16600548109119 / 20000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (224116123793 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_32 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (8296854858279 / 10000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (89646608633 / 4000000000000 : ℝ))
      (E := (cell12786 ⟨32, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (8296854858279 / 10000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (89646608633 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_33 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82934380470481 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241169262399 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨33, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82934380470481 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241169262399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_34 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (10362529522207 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241173261559 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨34, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (10362529522207 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241173261559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_35 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (10358264459183 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241177272711 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨35, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (10358264459183 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241177272711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_36 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (10354002365901 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241181237807 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨36, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (10354002365901 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241181237807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_37 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (82797945908347 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241185274539 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨37, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (82797945908347 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241185274539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_38 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (323296471041 / 390625000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120594632863 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨38, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (323296471041 / 390625000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120594632863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_39 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41364935465711 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (280149158747 / 12500000000000 : ℝ))
      (E := (cell12786 ⟨39, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41364935465711 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (280149158747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12787_20 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (8338042662429 / 10000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120498641899 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨20, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (8338042662429 / 10000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120498641899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_21 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41672985260643 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560250317829 / 25000000000000 : ℝ))
      (E := (cell12787 ⟨21, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41672985260643 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560250317829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_22 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83311538620137 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560251325277 / 25000000000000 : ℝ))
      (E := (cell12787 ⟨22, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83311538620137 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560251325277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_23 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41638565444019 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448201852027 / 20000000000000 : ℝ))
      (E := (cell12787 ⟨23, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41638565444019 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448201852027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_24 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (20810686823087 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241013268457 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨24, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (20810686823087 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241013268457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_25 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83208387800597 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (17928138167 / 800000000000 : ℝ))
      (E := (cell12787 ⟨25, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83208387800597 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (17928138167 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_26 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (259918913689 / 312500000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (224102127029 / 10000000000000 : ℝ))
      (E := (cell12787 ⟨26, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (259918913689 / 312500000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (224102127029 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_27 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83139740999857 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (224102526937 / 10000000000000 : ℝ))
      (E := (cell12787 ⟨27, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83139740999857 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (224102526937 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_28 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41552726813377 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241029270549 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨28, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41552726813377 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241029270549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_29 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41535595114679 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241033276033 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨29, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41535595114679 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241033276033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_30 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83036950776021 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560259321949 / 25000000000000 : ℝ))
      (E := (cell12787 ⟨30, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83036950776021 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560259321949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_31 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41501367617627 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (35016270431 / 1562500000000 : ℝ))
      (E := (cell12787 ⟨31, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41501367617627 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (35016270431 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_32 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82968543575731 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241045336913 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨32, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82968543575731 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241045336913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_33 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82934375766283 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241049318483 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨33, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82934375766283 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241049318483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_34 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82900231775901 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (22410533119 / 1000000000000 : ℝ))
      (E := (cell12787 ⟨34, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82900231775901 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (22410533119 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_35 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82866111573733 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560264329501 / 25000000000000 : ℝ))
      (E := (cell12787 ⟨35, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82866111573733 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560264329501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_36 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82832015129083 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241061337407 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨36, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82832015129083 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241061337407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_37 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (20699485602853 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448213062363 / 20000000000000 : ℝ))
      (E := (cell12787 ⟨37, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (20699485602853 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448213062363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_38 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41381946695167 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241069358741 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨38, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41381946695167 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2241069358741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_39 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (82729868035619 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448214672147 / 20000000000000 : ℝ))
      (E := (cell12787 ⟨39, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (82729868035619 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448214672147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12788_20 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83380417951481 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (35013708713 / 1562500000000 : ℝ))
      (E := (cell12788 ⟨20, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83380417951481 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (35013708713 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_21 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (16669192431279 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120440694307 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨21, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (16669192431279 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120440694307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_22 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (5206970660171 / 6250000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (17506917221 / 781250000000 : ℝ))
      (E := (cell12788 ⟨22, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (5206970660171 / 6250000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (17506917221 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_23 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41638561568849 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240889408257 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨23, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41638561568849 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240889408257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_24 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41621369924321 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240893403891 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨24, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41621369924321 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240893403891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_25 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83208380663099 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120448697161 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨25, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83208380663099 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120448697161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_26 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83174045548763 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560225345613 / 25000000000000 : ℝ))
      (E := (cell12788 ⟨26, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83174045548763 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560225345613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_27 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83139734473497 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120452685473 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨27, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83139734473497 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120452685473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_28 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83105447405327 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120454710357 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨28, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83105447405327 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120454710357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_29 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83071184312441 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120456708517 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨29, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83071184312441 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120456708517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_30 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83036945163191 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560229355083 / 25000000000000 : ℝ))
      (E := (cell12788 ⟨30, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83036945163191 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560229355083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_31 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (8300272992609 / 10000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240921432351 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨31, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (8300272992609 / 10000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240921432351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_32 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (20742134642453 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (56023134901 / 2500000000000 : ℝ))
      (E := (cell12788 ⟨32, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (20742134642453 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (56023134901 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_33 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82934371063189 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120464714901 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨33, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82934371063189 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120464714901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_34 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82900227375213 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120466708769 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨34, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82900227375213 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120466708769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_35 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82866107475033 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120468709327 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨35, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82866107475033 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120468709327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_36 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82832011331953 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240941433763 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨36, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82832011331953 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240941433763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_37 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (16559587783087 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448189092651 / 20000000000000 : ℝ))
      (E := (cell12788 ⟨37, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (16559587783087 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448189092651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_38 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (16552778039019 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448189889717 / 20000000000000 : ℝ))
      (E := (cell12788 ⟨38, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (16552778039019 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448189889717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_39 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (82729865140701 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120476724181 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨39, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (82729865140701 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120476724181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12789_20 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41690204640127 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240757485909 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨20, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41690204640127 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240757485909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_21 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (1666919075861 / 2000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120380751053 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨21, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (1666919075861 / 2000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120380751053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_22 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83311522506843 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (22407655037 / 1000000000000 : ℝ))
      (E := (cell12789 ⟨22, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83311522506843 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (22407655037 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_23 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83277115388829 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560192373573 / 25000000000000 : ℝ))
      (E := (cell12789 ⟨23, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83277115388829 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560192373573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_24 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83242732406371 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (140048345977 / 6250000000000 : ℝ))
      (E := (cell12789 ⟨24, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83242732406371 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (140048345977 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_25 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41604186763499 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120388757057 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨25, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41604186763499 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120388757057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_26 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83174038718407 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (140048846839 / 6250000000000 : ℝ))
      (E := (cell12789 ⟨26, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83174038718407 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (140048846839 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_27 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83139727948461 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120392763697 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨27, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83139727948461 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120392763697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_28 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83105441185187 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240789508863 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨28, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83105441185187 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240789508863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_29 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41535589198387 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560198388633 / 25000000000000 : ℝ))
      (E := (cell12789 ⟨29, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41535589198387 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560198388633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_30 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (3321477582063 / 4000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240797549401 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨30, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (3321477582063 / 4000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240797549401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_31 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83002724618103 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (224080155369 / 10000000000000 : ℝ))
      (E := (cell12789 ⟨31, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83002724618103 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (224080155369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_32 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82968533565033 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240805568913 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨32, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82968533565033 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240805568913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_33 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82934366361199 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240809537767 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨33, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82934366361199 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240809537767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_34 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82900222975593 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120406789237 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨34, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82900222975593 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120406789237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_35 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (20716525844341 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240817574663 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨35, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (20716525844341 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240817574663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_36 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41416003767909 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240821585539 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨36, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41416003767909 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240821585539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_37 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82797935420417 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560206388201 / 25000000000000 : ℝ))
      (E := (cell12789 ⟨37, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82797935420417 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560206388201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_38 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41381943500389 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240829593971 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨38, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41381943500389 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240829593971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_39 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (82729862246671 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240833591589 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨39, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (82729862246671 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240833591589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12790_20 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83380400610609 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560159417157 / 25000000000000 : ℝ))
      (E := (cell12790 ⟨20, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83380400610609 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560159417157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_21 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83345945431249 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120320835051 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨21, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83345945431249 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120320835051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_22 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41655757226229 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560161414419 / 25000000000000 : ℝ))
      (E := (cell12790 ⟨22, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41655757226229 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560161414419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_23 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83277107641431 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240649693311 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨23, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83277107641431 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240649693311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_24 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83242724965533 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (7002042699 / 312500000000 : ℝ))
      (E := (cell12790 ⟨24, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83242724965533 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (7002042699 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_25 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83208366392293 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (140041105541 / 6250000000000 : ℝ))
      (E := (cell12790 ⟨25, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83208366392293 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (140041105541 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_26 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83174031889411 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (44813233087 / 2000000000000 : ℝ))
      (E := (cell12790 ⟨26, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83174031889411 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (44813233087 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_27 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (20784930356187 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120332840131 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨27, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (20784930356187 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120332840131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_28 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83105434966333 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120334855209 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨28, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83105434966333 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120334855209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_29 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (20767793120589 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (89626947541 / 4000000000000 : ℝ))
      (E := (cell12790 ⟨29, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (20767793120589 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (89626947541 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_30 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83036933941171 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560169418751 / 25000000000000 : ℝ))
      (E := (cell12790 ⟨30, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83036933941171 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560169418751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_31 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83002719311293 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240681730143 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨31, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83002719311293 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240681730143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_32 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16593705712279 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (140042854989 / 6250000000000 : ℝ))
      (E := (cell12790 ⟨32, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16593705712279 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (140042854989 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_33 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (82934361660313 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (280086212621 / 12500000000000 : ℝ))
      (E := (cell12790 ⟨33, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (82934361660313 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (280086212621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_34 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (1036252732213 / 1250000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240693736091 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨34, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (1036252732213 / 1250000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240693736091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_35 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41433049640363 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240697727391 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨35, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41433049640363 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240697727391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_36 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (82832003740677 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240701734071 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨36, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (82832003740677 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240701734071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_37 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41398965963179 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240705756517 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨37, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41398965963179 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240705756517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_38 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (82763883807383 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240709736187 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨38, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (82763883807383 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240709736187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_39 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41364929676763 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560178432921 / 25000000000000 : ℝ))
      (E := (cell12790 ⟨39, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41364929676763 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560178432921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12791_20 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41690195971273 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140032365469 / 6250000000000 : ℝ))
      (E := (cell12791 ⟨20, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41690195971273 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140032365469 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_21 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83345937070993 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240521834293 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨21, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83345937070993 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240521834293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_22 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (4165575319979 / 5000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240525866221 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨22, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (4165575319979 / 5000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240525866221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_23 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (5204818743469 / 6250000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (11202649443 / 500000000000 : ℝ))
      (E := (cell12791 ⟨23, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (5204818743469 / 6250000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (11202649443 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_24 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (5202669845383 / 6250000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120266923209 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨24, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (5202669845383 / 6250000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120266923209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_25 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (16641671851797 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (280067232443 / 12500000000000 : ℝ))
      (E := (cell12791 ⟨25, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (16641671851797 / 20000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (280067232443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_26 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41587012530887 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120270936259 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨26, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41587012530887 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120270936259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_27 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41569857451179 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (560136472001 / 25000000000000 : ℝ))
      (E := (cell12791 ⟨27, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41569857451179 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (560136472001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_28 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41552714374383 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120274954217 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨28, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41552714374383 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120274954217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_29 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83071166569189 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240553877513 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨29, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83071166569189 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240553877513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_30 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83036928331981 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (280069739273 / 12500000000000 : ℝ))
      (E := (cell12791 ⟨30, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83036928331981 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (280069739273 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_31 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41501357002829 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (224056190317 / 10000000000000 : ℝ))
      (E := (cell12791 ⟨31, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41501357002829 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (224056190317 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_32 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (5185532722431 / 6250000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240565904483 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨32, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (5185532722431 / 6250000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240565904483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_33 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (8293435696053 / 10000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240569919409 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨33, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (8293435696053 / 10000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240569919409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_34 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41450107089777 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120286945197 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨34, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41450107089777 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120286945197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_35 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41433047592559 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240577935481 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨35, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41433047592559 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240577935481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_36 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (82831999946531 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (89623277521 / 4000000000000 : ℝ))
      (E := (cell12791 ⟨36, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (82831999946531 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (89623277521 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_37 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (10349741054157 / 12500000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120292949171 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨37, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (10349741054157 / 12500000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120292949171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_38 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (8276388061491 / 10000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120294966973 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨38, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (8276388061491 / 10000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120294966973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_39 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41364928230633 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240593927383 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨39, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41364928230633 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240593927383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12792_20 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83380383276063 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120199040413 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨20, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83380383276063 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120199040413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_21 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83345928712281 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240402052991 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨21, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83345928712281 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240402052991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_22 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83311498348209 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240406070999 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨22, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83311498348209 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240406070999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_23 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41638546075523 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120205040081 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨23, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41638546075523 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120205040081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_24 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (20810677522039 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240414083847 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨24, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (20810677522039 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240414083847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_25 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83208352127073 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (448083617037 / 20000000000000 : ℝ))
      (E := (cell12792 ⟨25, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83208352127073 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (448083617037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_26 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83174018235497 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (224042208707 / 10000000000000 : ℝ))
      (E := (cell12792 ⟨26, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83174018235497 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (224042208707 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_27 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (8313970838129 / 10000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240426092169 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨27, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (8313970838129 / 10000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240426092169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_28 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (20776355633121 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240430102911 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨28, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (20776355633121 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240430102911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_29 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (8307116065727 / 10000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120217060749 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨29, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (8307116065727 / 10000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120217060749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_30 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83036922724003 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120219045689 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨30, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83036922724003 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120219045689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_31 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (207506771753 / 250000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120221065657 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨31, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (207506771753 / 250000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120221065657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_32 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82968518557537 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240446125751 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨32, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82968518557537 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240446125751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_33 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (1658687045237 / 2000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120225067249 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨33, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (1658687045237 / 2000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120225067249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_34 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41450104891567 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240454158613 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨34, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41450104891567 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240454158613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_35 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82866091090541 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560114535073 / 25000000000000 : ℝ))
      (E := (cell12792 ⟨35, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82866091090541 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560114535073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_36 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82831996153379 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240462138737 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨36, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82831996153379 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240462138737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_37 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (10349740617639 / 12500000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (448093230867 / 20000000000000 : ℝ))
      (E := (cell12792 ⟨37, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (10349740617639 / 12500000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (448093230867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_38 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (82763877423359 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120235064269 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨38, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (82763877423359 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120235064269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_39 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (20682463392473 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560118544671 / 25000000000000 : ℝ))
      (E := (cell12792 ⟨39, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (20682463392473 / 25000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560118544671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12793_20 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41690187305581 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120139155153 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨20, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41690187305581 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120139155153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_21 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (10418240044389 / 12500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560070581549 / 25000000000000 : ℝ))
      (E := (cell12793 ⟨21, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (10418240044389 / 12500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560070581549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_22 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (16662298059669 / 20000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448057266069 / 20000000000000 : ℝ))
      (E := (cell12793 ⟨22, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (16662298059669 / 20000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (448057266069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_23 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41638542204029 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120145163177 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨23, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41638542204029 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120145163177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_24 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83242702651617 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240294317587 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨24, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83242702651617 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240294317587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_25 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83208344996557 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120149182789 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨25, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83208344996557 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120149182789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_26 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41587005705289 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560075589109 / 25000000000000 : ℝ))
      (E := (cell12793 ⟨26, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41587005705289 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560075589109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_27 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (16627940372309 / 20000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (280038293901 / 12500000000000 : ℝ))
      (E := (cell12793 ⟨27, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (16627940372309 / 20000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (280038293901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_28 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (5194088519843 / 6250000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240310352323 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨28, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (5194088519843 / 6250000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240310352323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_29 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (415355773733 / 500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240314361981 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨29, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (415355773733 / 500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240314361981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_30 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83036917117237 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240318382153 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨30, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83036917117237 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240318382153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_31 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83002703397917 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (35005036813 / 1562500000000 : ℝ))
      (E := (cell12793 ⟨31, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83002703397917 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (35005036813 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_32 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82968513557317 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240326343631 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨32, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82968513557317 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240326343631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_33 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82934347564273 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240330404827 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨33, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82934347564273 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240330404827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_34 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82900205387781 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240334364901 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨34, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82900205387781 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240334364901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_35 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82866086996993 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120169200233 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨35, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82866086996993 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120169200233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_36 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (4141599618061 / 5000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240342394873 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨36, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (4141599618061 / 5000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240342394873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_37 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (3311916857997 / 4000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (17922771257 / 800000000000 : ℝ))
      (E := (cell12793 ⟨37, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (3311916857997 / 4000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (17922771257 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_38 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82763874232729 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120175189337 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨38, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82763874232729 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120175189337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_39 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (82729850679403 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120177213429 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨39, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (82729850679403 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120177213429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12794_20 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (260563643587 / 312500000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560039648559 / 25000000000000 : ℝ))
      (E := (cell12794 ⟨20, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (260563643587 / 312500000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560039648559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_21 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41672955999743 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240162595601 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨21, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41672955999743 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240162595601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_22 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41655741124993 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240166585929 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨22, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41655741124993 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240166585929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_23 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83277076666539 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120085313589 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨23, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83277076666539 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120085313589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_24 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83242695216511 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240174606019 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨24, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83242695216511 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240174606019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_25 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83208337867437 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (28002233029 / 1250000000000 : ℝ))
      (E := (cell12794 ⟨25, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83208337867437 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (28002233029 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_26 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41587002293509 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240182622191 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨26, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41587002293509 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240182622191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_27 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83139695343121 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240186606673 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨27, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83139695343121 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240186606673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_28 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (2597044065743 / 3125000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120095328337 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨28, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (2597044065743 / 3125000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120095328337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_29 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41535574418589 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (280024332183 / 12500000000000 : ℝ))
      (E := (cell12794 ⟨29, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41535574418589 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (280024332183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_30 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83036911511683 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448039733893 / 20000000000000 : ℝ))
      (E := (cell12794 ⟨30, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83036911511683 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448039733893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_31 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (8300269809581 / 10000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240202635871 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨31, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (8300269809581 / 10000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240202635871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_32 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (16593701711647 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120103337631 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨32, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (16593701711647 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120103337631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_33 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41467171433899 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120105335903 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨33, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41467171433899 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120105335903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_34 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82900200993493 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (224021468511 / 10000000000000 : ℝ))
      (E := (cell12794 ⟨34, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82900200993493 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (224021468511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_35 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (20716520726119 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240218657363 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨35, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (20716520726119 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240218657363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_36 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41415994285027 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240222647771 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨36, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41415994285027 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240222647771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_37 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (5174869872481 / 6250000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240226656713 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨37, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (5174869872481 / 6250000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240226656713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_38 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82763871043019 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560057671089 / 25000000000000 : ℝ))
      (E := (cell12794 ⟨38, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82763871043019 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560057671089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_39 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (82729847789799 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240234671903 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨39, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (82729847789799 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240234671903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12795_20 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83380357286099 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240038932611 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨20, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83380357286099 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240038932611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_21 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (20836475911351 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120021459757 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨21, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (20836475911351 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120021459757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_22 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41655737101567 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240046954417 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨22, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41655737101567 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240046954417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_23 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (10409633615811 / 12500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240050924277 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨23, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (10409633615811 / 12500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240050924277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_24 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (20810671945709 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448010989829 / 20000000000000 : ℝ))
      (E := (cell12795 ⟨24, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (20810671945709 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448010989829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_25 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83208330739711 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240058915413 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨25, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83208330739711 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240058915413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_26 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (5198374860301 / 6250000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (56001573569 / 2500000000000 : ℝ))
      (E := (cell12795 ⟨26, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (5198374860301 / 6250000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (56001573569 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_27 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83139688826019 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448013383403 / 20000000000000 : ℝ))
      (E := (cell12795 ⟨27, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83139688826019 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448013383403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_28 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (1662108077827 / 2000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120035478743 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨28, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (1662108077827 / 2000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120035478743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_29 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (16614228585801 / 20000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120037474723 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨29, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (16614228585801 / 20000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120037474723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_30 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83036905907341 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448015790663 / 20000000000000 : ℝ))
      (E := (cell12795 ⟨30, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83036905907341 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448015790663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_31 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83002692794877 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (224008297083 / 10000000000000 : ℝ))
      (E := (cell12795 ⟨31, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83002692794877 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (224008297083 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_32 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (20742125890073 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448017388987 / 20000000000000 : ℝ))
      (E := (cell12795 ⟨32, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (20742125890073 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448017388987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_33 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (3317373526897 / 4000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240090994027 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨33, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (3317373526897 / 4000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240090994027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_34 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (5181262287517 / 6250000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240095002003 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨34, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (5181262287517 / 6250000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240095002003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_35 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82866078812987 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (17920791757 / 800000000000 : ℝ))
      (E := (cell12795 ⟨35, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82866078812987 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (17920791757 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_36 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41415992389941 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (560025739023 / 25000000000000 : ℝ))
      (E := (cell12795 ⟨36, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41415992389941 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (560025739023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_37 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82797914470423 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240106961787 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨37, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82797914470423 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240106961787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_38 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (82763867854231 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (280013873359 / 12500000000000 : ℝ))
      (E := (cell12795 ⟨38, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (82763867854231 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (280013873359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_39 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (2068246122527 / 2500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120057486277 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨39, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (2068246122527 / 2500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120057486277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12796_20 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83380348625937 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (44798385343 / 2000000000000 : ℝ))
      (E := (cell12796 ⟨20, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83380348625937 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (44798385343 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_21 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83345895292863 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559980809907 / 25000000000000 : ℝ))
      (E := (cell12796 ⟨21, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83345895292863 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559980809907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_22 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83311466157787 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (223992726081 / 10000000000000 : ℝ))
      (E := (cell12796 ⟨22, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83311466157787 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (223992726081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_23 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83277061187907 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (279991409501 / 12500000000000 : ℝ))
      (E := (cell12796 ⟨23, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83277061187907 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (279991409501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_24 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (650333440239 / 781250000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (447987057717 / 20000000000000 : ℝ))
      (E := (cell12796 ⟨24, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (650333440239 / 781250000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (447987057717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_25 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (4160416180669 / 5000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239939301667 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨25, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (4160416180669 / 5000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239939301667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_26 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (20793497735993 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239943259719 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨26, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (20793497735993 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239943259719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_27 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83139682310237 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559986820559 / 25000000000000 : ℝ))
      (E := (cell12796 ⟨27, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83139682310237 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559986820559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_28 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (5194087355013 / 6250000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239951313239 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨28, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (5194087355013 / 6250000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239951313239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_29 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83071137022079 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (223995529643 / 10000000000000 : ℝ))
      (E := (cell12796 ⟨29, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83071137022079 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (223995529643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_30 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (8303690030421 / 10000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119979646113 / 50000000000000 : ℝ))
      (E := (cell12796 ⟨30, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (8303690030421 / 10000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119979646113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_31 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83002687495119 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239963302367 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨31, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83002687495119 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239963302367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_32 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (2592765580109 / 3125000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239967328361 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨32, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (2592765580109 / 3125000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239967328361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_33 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (41467166739077 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (22399713129 / 1000000000000 : ℝ))
      (E := (cell12796 ⟨33, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (41467166739077 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (22399713129 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_34 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (16580038441623 / 20000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559993828897 / 25000000000000 : ℝ))
      (E := (cell12796 ⟨34, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (16580038441623 / 20000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559993828897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_35 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (2589564835079 / 3125000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559994834313 / 25000000000000 : ℝ))
      (E := (cell12796 ⟨35, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (2589564835079 / 3125000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559994834313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_36 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82831980990703 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119991659919 / 50000000000000 : ℝ))
      (E := (cell12796 ⟨36, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82831980990703 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119991659919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_37 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82797910982107 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239987322347 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨37, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82797910982107 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239987322347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_38 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (82763864666363 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (279998918117 / 12500000000000 : ℝ))
      (E := (cell12796 ⟨38, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (82763864666363 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (279998918117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_39 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (16545968402649 / 20000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239995328813 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨39, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (16545968402649 / 20000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239995328813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12797_20 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41690169983677 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111989982807 / 5000000000000 : ℝ))
      (E := (cell12797 ⟨20, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41690169983677 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111989982807 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_21 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (16669177388373 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239803614253 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨21, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (16669177388373 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239803614253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_22 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (10413932264243 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239807621777 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨22, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (10413932264243 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239807621777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_23 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83277053450793 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119905812009 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨23, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83277053450793 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119905812009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_24 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (4162133645989 / 5000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111990781217 / 5000000000000 : ℝ))
      (E := (cell12797 ⟨24, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (4162133645989 / 5000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111990781217 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_25 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83208316488443 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239819625869 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨25, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83208316488443 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239819625869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_26 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41586992062243 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239823631497 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨26, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41586992062243 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239823631497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_27 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83139675795777 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559956910971 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨27, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83139675795777 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559956910971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_28 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (1662107829407 / 2000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239831665457 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨28, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (1662107829407 / 2000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239831665457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_29 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83071131116401 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559958909979 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨29, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83071131116401 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559958909979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_30 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (8303689470229 / 10000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (11199198431 / 500000000000 : ℝ))
      (E := (cell12797 ⟨30, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (8303689470229 / 10000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (11199198431 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_31 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (10375335274567 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119921844513 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨31, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (10375335274567 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119921844513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_32 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82968493567821 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119923854201 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨32, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82968493567821 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119923854201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_33 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (10366791098123 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239851687019 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨33, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (10366791098123 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239851687019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_34 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (1295315434641 / 1562500000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559963921119 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨34, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (1295315434641 / 1562500000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559963921119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_35 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82866070633097 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119929850803 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨35, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82866070633097 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119929850803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_36 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (20707994300629 / 25000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (44797273607 / 2000000000000 : ℝ))
      (E := (cell12797 ⟨36, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (20707994300629 / 25000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (44797273607 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_37 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (82797907494747 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559966919927 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨37, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (82797907494747 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559966919927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_38 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (16552772295883 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119935849919 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨38, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (16552772295883 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119935849919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_39 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41364919563147 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (55996893517 / 2500000000000 : ℝ))
      (E := (cell12797 ⟨39, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41364919563147 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (55996893517 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12798_20 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (1667606626207 / 2000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239680041293 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨20, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (1667606626207 / 2000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239680041293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_21 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83345878592409 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (17497531589 / 781250000000 : ℝ))
      (E := (cell12798 ⟨21, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83345878592409 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (17497531589 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_22 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83311450071607 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559922009329 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨22, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83311450071607 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559922009329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_23 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83277045715147 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119846013331 / 50000000000000 : ℝ))
      (E := (cell12798 ⟨23, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83277045715147 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119846013331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_24 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83242665490399 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559924018293 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨24, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83242665490399 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559924018293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_25 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (832083093649 / 1000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239700063233 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨25, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (832083093649 / 1000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239700063233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_26 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83173977306357 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239704058093 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨26, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83173977306357 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239704058093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_27 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83139669282637 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559927015103 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨27, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83139669282637 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559927015103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_28 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (3324215410471 / 4000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239712072617 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨28, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (3324215410471 / 4000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239712072617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_29 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (8307112521197 / 10000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239716096903 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨29, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (8307112521197 / 10000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239716096903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_30 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (4151844455079 / 5000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (447944015343 / 20000000000000 : ℝ))
      (E := (cell12798 ⟨30, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (4151844455079 / 5000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (447944015343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_31 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83002676899127 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (279965509033 / 12500000000000 : ℝ))
      (E := (cell12798 ⟨31, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83002676899127 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (279965509033 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_32 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (20742122143323 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239728085059 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨32, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (20742122143323 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239728085059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_33 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (20733581023229 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239732057789 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨33, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (20733581023229 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239732057789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_34 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (41450091713499 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239736108671 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨34, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (41450091713499 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239736108671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_35 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (16573213308939 / 20000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119870060663 / 50000000000000 : ℝ))
      (E := (cell12798 ⟨35, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (16573213308939 / 20000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119870060663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_36 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82831973415321 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239744096289 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨36, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82831973415321 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239744096289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_37 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (10349738001043 / 12500000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559937023139 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨37, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (10349738001043 / 12500000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559937023139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_38 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82763858293387 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (139984506893 / 6250000000000 : ℝ))
      (E := (cell12798 ⟨38, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82763858293387 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (139984506893 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_39 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (82729836240227 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239756090689 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨39, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (82729836240227 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239756090689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12799_20 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (20845080663731 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239560480899 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨20, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (20845080663731 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239560480899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_21 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83345870244493 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119782234367 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨21, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83345870244493 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119782234367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_22 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41655721015387 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239568449097 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨22, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41655721015387 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239568449097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_23 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (10409629747621 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (279946560493 / 12500000000000 : ℝ))
      (E := (cell12799 ⟨23, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (10409629747621 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (279946560493 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_24 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83242658062447 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239576459941 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨24, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83242658062447 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239576459941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_25 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83208302242751 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (279947562119 / 12500000000000 : ℝ))
      (E := (cell12799 ⟨25, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83208302242751 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (279947562119 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_26 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (5198373155599 / 6250000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119792240541 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨26, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (5198373155599 / 6250000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119792240541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_27 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83139662770817 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (223958847337 / 10000000000000 : ℝ))
      (E := (cell12799 ⟨27, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83139662770817 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (223958847337 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_28 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (16621075810897 / 20000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239592476243 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨28, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (16621075810897 / 20000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239592476243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_29 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41535559654393 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (279949561487 / 12500000000000 : ℝ))
      (E := (cell12799 ⟨29, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41535559654393 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (279949561487 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_30 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (16218141309 / 19531250000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (447920104459 / 20000000000000 : ℝ))
      (E := (cell12799 ⟨30, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (16218141309 / 19531250000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (447920104459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_31 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83002671602891 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239604510627 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨31, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83002671602891 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239604510627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_32 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (829684835799 / 1000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119804258451 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨32, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (829684835799 / 1000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119804258451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_33 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (20733579850487 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239612542399 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨33, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (20733579850487 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239612542399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_34 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (20725044759509 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119808264779 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨34, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (20725044759509 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119808264779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_35 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41433031228661 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (89584821511 / 4000000000000 : ℝ))
      (E := (cell12799 ⟨35, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41433031228661 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (89584821511 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_36 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41415984814559 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239624508993 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨36, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41415984814559 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239624508993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_37 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (5174868782681 / 6250000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119814280447 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨37, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (5174868782681 / 6250000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119814280447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_38 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (82763855108279 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119816258789 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨38, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (82763855108279 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119816258789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_39 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (20682458338761 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239636555041 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨39, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (20682458338761 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239636555041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

end BstLean.Part268
