import BstLean.Part268CellShard17Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12775_0 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (42037431195583 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (112117921689 / 5000000000000 : ℝ))
      (E := (cell12775 ⟨0, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (42037431195583 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (112117921689 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_1 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (84039911288881 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121181190657 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨1, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (84039911288881 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121181190657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_2 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (84004985087083 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242366410797 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨2, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (84004985087083 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242366410797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_3 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41985041874673 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560592603823 / 25000000000000 : ℝ))
      (E := (cell12775 ⟨3, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41985041874673 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560592603823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_4 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (16787041447887 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121187201621 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨4, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (16787041447887 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121187201621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_5 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (10487544440163 / 12500000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560594595709 / 25000000000000 : ℝ))
      (E := (cell12775 ⟨5, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (10487544440163 / 12500000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560594595709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_6 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41932764279549 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (56059560499 / 2500000000000 : ℝ))
      (E := (cell12775 ⟨6, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41932764279549 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (56059560499 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_7 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (83830726317151 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242386406397 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨7, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (83830726317151 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242386406397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_8 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (83795948759981 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121195203753 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨8, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (83795948759981 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121195203753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_9 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41880597926147 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (280299303807 / 12500000000000 : ℝ))
      (E := (cell12775 ⟨9, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41880597926147 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (280299303807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_10 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (83726467558979 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448479684823 / 20000000000000 : ℝ))
      (E := (cell12775 ⟨10, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (83726467558979 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448479684823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_11 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (8369176384511 / 10000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121201197541 / 50000000000000 : ℝ))
      (E := (cell12775 ⟨11, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (8369176384511 / 10000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (1121201197541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_12 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41828542337971 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448481281561 / 20000000000000 : ℝ))
      (E := (cell12775 ⟨12, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41828542337971 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448481281561 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_13 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (8362243001691 / 10000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (70075325323 / 3125000000000 : ℝ))
      (E := (cell12775 ⟨13, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (8362243001691 / 10000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (70075325323 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_14 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (8358779983363 / 10000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560603602133 / 25000000000000 : ℝ))
      (E := (cell12775 ⟨14, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (8358779983363 / 10000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (560603602133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_15 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (16710638818379 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242418408003 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨15, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (16710638818379 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242418408003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_16 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (41759306378839 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448484482823 / 20000000000000 : ℝ))
      (E := (cell12775 ⟨16, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (41759306378839 / 50000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (448484482823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_17 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (83484055797127 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242426431991 / 100000000000000 : ℝ))
      (E := (cell12775 ⟨17, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (83484055797127 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (2242426431991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_18 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (83449523176563 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (89697216331 / 4000000000000 : ℝ))
      (E := (cell12775 ⟨18, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (83449523176563 / 100000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (89697216331 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12775_19 : CellCertificate 12775 (176921420541783 / 2000000000000000 : ℝ) (1644179112247967 / 1000000000000000000 : ℝ) (166034839257223 / 5000000000000000 : ℝ)
    (cell12775 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · norm_num [cell12775]
  · have h := gap_lower (n := 12775) (a := (16683002972497 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (112121723203 / 5000000000000 : ℝ))
      (E := (cell12775 ⟨19, by decide⟩).energy) (xi := (166034839257223 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12775 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12775]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12775])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12775) (a := (16683002972497 / 20000000000000 : ℝ)) (b := (806128287 / 500000000000 : ℝ)) (q := (112121723203 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12775])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12775]

theorem cert12776_0 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (84074847440417 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560559535509 / 25000000000000 : ℝ))
      (E := (cell12776 ⟨0, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (84074847440417 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560559535509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_1 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (42019948327641 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242242117471 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨1, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (42019948327641 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242242117471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_2 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (42002485385093 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (3503509559 / 156250000000 : ℝ))
      (E := (cell12776 ⟨2, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (42002485385093 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (3503509559 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_3 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (2624064679647 / 3125000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (224225015167 / 10000000000000 : ℝ))
      (E := (cell12776 ⟨3, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (2624064679647 / 3125000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (224225015167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_4 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (419675967773 / 500000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121127084903 / 50000000000000 : ℝ))
      (E := (cell12776 ⟨4, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (419675967773 / 500000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (1121127084903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_5 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (10487542768979 / 12500000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448451624483 / 20000000000000 : ℝ))
      (E := (cell12776 ⟨5, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (10487542768979 / 12500000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448451624483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_6 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (16773103100909 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (89690485331 / 4000000000000 : ℝ))
      (E := (cell12776 ⟨6, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (16773103100909 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (89690485331 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_7 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (5239419598567 / 6250000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560566538037 / 25000000000000 : ℝ))
      (E := (cell12776 ⟨7, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (5239419598567 / 6250000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560566538037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_8 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (16759187266787 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242270128451 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨8, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (16759187266787 / 20000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242270128451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_9 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83761183739839 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (140142132957 / 6250000000000 : ℝ))
      (E := (cell12776 ⟨9, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83761183739839 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (140142132957 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_10 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (3349058230387 / 4000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242278155649 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨10, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (3349058230387 / 4000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242278155649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_11 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83691752358517 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448456432411 / 20000000000000 : ℝ))
      (E := (cell12776 ⟨11, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83691752358517 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448456432411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_12 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83657073501621 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (28028576911 / 1250000000000 : ℝ))
      (E := (cell12776 ⟨12, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83657073501621 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (28028576911 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_13 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83622419154423 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242290134227 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨13, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83622419154423 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242290134227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_14 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (4179389464127 / 5000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448458834019 / 20000000000000 : ℝ))
      (E := (cell12776 ⟨14, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (4179389464127 / 5000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (448458834019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_15 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83553183851767 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242298149827 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨15, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83553183851767 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242298149827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_16 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (83518602828077 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (224230213691 / 10000000000000 : ℝ))
      (E := (cell12776 ⟨16, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (83518602828077 / 100000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (224230213691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_17 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41742023088809 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242306136467 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨17, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41742023088809 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242306136467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_18 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41724756933357 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242310153379 / 100000000000000 : ℝ))
      (E := (cell12776 ⟨18, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41724756933357 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (2242310153379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12776_19 : CellCertificate 12776 (442289741030821 / 5000000000000000 : ℝ) (411012594348613 / 250000000000000000 : ℝ) (41505382599077 / 1250000000000000 : ℝ)
    (cell12776 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · norm_num [cell12776]
  · have h := gap_lower (n := 12776) (a := (41707502930931 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560578548071 / 25000000000000 : ℝ))
      (E := (cell12776 ⟨19, by decide⟩).energy) (xi := (41505382599077 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12776 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12776]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12776])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12776) (a := (41707502930931 / 50000000000000 : ℝ)) (b := (80606443003 / 50000000000000 : ℝ)) (q := (560578548071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12776])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12776]

theorem cert12777_0 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (21018708123003 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242117903477 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨0, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (21018708123003 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242117903477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_1 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (84039882023989 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (3587395051 / 160000000000 : ℝ))
      (E := (cell12777 ⟨1, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (84039882023989 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (3587395051 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_2 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (21001239113889 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (140132867377 / 6250000000000 : ℝ))
      (E := (cell12777 ⟨2, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (21001239113889 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (140132867377 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_3 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (8397005575029 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242129883533 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨3, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (8397005575029 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242129883533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_4 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (20983794967989 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560533482973 / 25000000000000 : ℝ))
      (E := (cell12777 ⟨4, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (20983794967989 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (560533482973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_5 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (83900328784513 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242137915491 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨5, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (83900328784513 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242137915491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_6 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41932751226053 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242141900149 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨6, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41932751226053 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242141900149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_7 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (8383070083907 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121072946769 / 50000000000000 : ℝ))
      (E := (cell12777 ⟨7, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (8383070083907 / 10000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121072946769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_8 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (83795923909927 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (56053747577 / 2500000000000 : ℝ))
      (E := (cell12777 ⟨8, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (83795923909927 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (56053747577 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_9 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (10470146453673 / 12500000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242153935943 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨9, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (10470146453673 / 12500000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242153935943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_10 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (83726443962333 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (8758429457 / 390625000000 : ℝ))
      (E := (cell12777 ⟨10, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (83726443962333 / 100000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (8758429457 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_11 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (10461467609231 / 12500000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (89686476993 / 4000000000000 : ℝ))
      (E := (cell12777 ⟨11, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (10461467609231 / 12500000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (89686476993 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_12 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41828531164593 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242165893791 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨12, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41828531164593 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242165893791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_13 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (16724481658757 / 20000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242169912113 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨13, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (16724481658757 / 20000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242169912113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_14 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41793889366631 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242173927569 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨14, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41793889366631 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242173927569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_15 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41776586806707 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242177945769 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨15, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41776586806707 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242177945769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_16 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (20879648225053 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121090956943 / 50000000000000 : ℝ))
      (E := (cell12777 ⟨16, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (20879648225053 / 25000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (1121090956943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_17 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (1304438071247 / 1562500000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242185953401 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨17, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (1304438071247 / 1562500000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242185953401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_18 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (41724752279263 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242189952787 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨18, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (41724752279263 / 50000000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242189952787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12777_19 : CellCertificate 12777 (44227593278159 / 500000000000000 : ℝ) (1643921662698551 / 1000000000000000000 : ℝ) (166008223695193 / 5000000000000000 : ℝ)
    (cell12777 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · norm_num [cell12777]
  · have h := gap_lower (n := 12777) (a := (5213437303929 / 6250000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242193916611 / 100000000000000 : ℝ))
      (E := (cell12777 ⟨19, by decide⟩).energy) (xi := (166008223695193 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12777 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12777]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12777])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12777) (a := (5213437303929 / 6250000000000 : ℝ)) (b := (161200116649 / 100000000000000 : ℝ)) (q := (2242193916611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12777])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12777]

theorem cert12778_0 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (1681496350919 / 2000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (280249714763 / 12500000000000 : ℝ))
      (E := (cell12778 ⟨0, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (1681496350919 / 2000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (280249714763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_1 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (84039867394999 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (280250211461 / 12500000000000 : ℝ))
      (E := (cell12778 ⟨1, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (84039867394999 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (280250211461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_2 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (10500617767899 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242005691617 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨2, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (10500617767899 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242005691617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_3 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (10496255219263 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (112100486333 / 5000000000000 : ℝ))
      (E := (cell12778 ⟨3, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (10496255219263 / 12500000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (112100486333 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_4 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (41967583095751 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (70062927797 / 3125000000000 : ℝ))
      (E := (cell12778 ⟨4, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (41967583095751 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (70062927797 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_5 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (16780063083869 / 20000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242017704133 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨5, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (16780063083869 / 20000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242017704133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_6 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (4193274470089 / 5000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121010860293 / 50000000000000 : ℝ))
      (E := (cell12778 ⟨6, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (4193274470089 / 5000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121010860293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_7 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83830688103143 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121012844277 / 50000000000000 : ℝ))
      (E := (cell12778 ⟨7, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83830688103143 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121012844277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_8 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83795911487957 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242029731397 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨8, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83795911487957 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242029731397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_9 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (8376115952093 / 10000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448406736453 / 20000000000000 : ℝ))
      (E := (cell12778 ⟨9, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (8376115952093 / 10000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448406736453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_10 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83726432166953 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448407544419 / 20000000000000 : ℝ))
      (E := (cell12778 ⟨10, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83726432166953 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448407544419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_11 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83691729391103 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121020841697 / 50000000000000 : ℝ))
      (E := (cell12778 ⟨11, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83691729391103 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121020841697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_12 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (41828525579319 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242045688637 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨12, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (41828525579319 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242045688637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_13 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (20905599358749 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560512435999 / 25000000000000 : ℝ))
      (E := (cell12778 ⟨13, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (20905599358749 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (560512435999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_14 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (20896942046449 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121026869551 / 50000000000000 : ℝ))
      (E := (cell12778 ⟨14, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (20896942046449 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (1121026869551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_15 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (41776581688417 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (35032152151 / 1562500000000 : ℝ))
      (E := (cell12778 ⟨15, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (41776581688417 / 50000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (35032152151 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_16 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (20879645743521 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448412349009 / 20000000000000 : ℝ))
      (E := (cell12778 ⟨16, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (20879645743521 / 25000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (448412349009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_17 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83484026943697 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242065708149 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨17, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83484026943697 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242065708149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_18 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83449495251999 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242069748263 / 100000000000000 : ℝ))
      (E := (cell12778 ⟨18, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83449495251999 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (2242069748263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12778_19 : CellCertificate 12778 (884524253212549 / 10000000000000000 : ℝ) (1643792968155529 / 1000000000000000000 : ℝ) (16599491915331 / 500000000000000 : ℝ)
    (cell12778 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · norm_num [cell12778]
  · have h := gap_lower (n := 12778) (a := (83414987865489 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (224207375357 / 10000000000000 : ℝ))
      (E := (cell12778 ⟨19, by decide⟩).energy) (xi := (16599491915331 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12778 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12778]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12778])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12778) (a := (83414987865489 / 100000000000000 : ℝ)) (b := (161187349327 / 100000000000000 : ℝ)) (q := (224207375357 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12778])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12778]

theorem cert12779_0 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (84074802602229 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120938764051 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨0, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (84074802602229 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120938764051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_1 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (42019926384157 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241881529751 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨1, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (42019926384157 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241881529751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_2 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (42002463916547 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (44837710013 / 2000000000000 : ℝ))
      (E := (cell12779 ⟨2, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (42002463916547 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (44837710013 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_3 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (16794005552029 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120944753693 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨3, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (16794005552029 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120944753693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_4 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (83935152513237 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (448378700111 / 20000000000000 : ℝ))
      (E := (cell12779 ⟨4, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (83935152513237 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (448378700111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_5 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (10487537757041 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560474386569 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨5, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (10487537757041 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560474386569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_6 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (83865476353567 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560475384157 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨6, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (83865476353567 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560475384157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_7 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (20957668842323 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (448381107439 / 20000000000000 : ℝ))
      (E := (cell12779 ⟨7, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (20957668842323 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (448381107439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_8 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (10474487383503 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560477388849 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨8, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (10474487383503 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560477388849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_9 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41880573707237 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (140119596273 / 6250000000000 : ℝ))
      (E := (cell12779 ⟨9, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41880573707237 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (140119596273 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_10 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41863210186767 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (224191755701 / 10000000000000 : ℝ))
      (E := (cell12779 ⟨10, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41863210186767 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (224191755701 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_11 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41845858955141 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (280240194239 / 12500000000000 : ℝ))
      (E := (cell12779 ⟨11, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41845858955141 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (280240194239 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_12 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (10457129998747 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (112096276871 / 5000000000000 : ℝ))
      (E := (cell12779 ⟨12, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (10457129998747 / 12500000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (112096276871 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_13 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (16724477315611 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120964756817 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨13, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (16724477315611 / 20000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120964756817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_14 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (4179387882007 / 5000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241933546551 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨14, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (4179387882007 / 5000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241933546551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_15 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41776576571013 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120968762757 / 50000000000000 : ℝ))
      (E := (cell12779 ⟨15, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41776576571013 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (1120968762757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_16 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (83518573049691 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560485393049 / 25000000000000 : ℝ))
      (E := (cell12779 ⟨16, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (83518573049691 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (560485393049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_17 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (20871004332321 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241945575359 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨17, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (20871004332321 / 25000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241945575359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_18 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (83449485947133 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (70060923119 / 3125000000000 : ℝ))
      (E := (cell12779 ⟨18, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (83449485947133 / 100000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (70060923119 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12779_19 : CellCertificate 12779 (6910130039131 / 78125000000000 : ℝ) (821832146880327 / 500000000000000000 : ℝ) (66392646708037 / 2000000000000000 : ℝ)
    (cell12779 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · norm_num [cell12779]
  · have h := gap_lower (n := 12779) (a := (41707489434869 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241953528373 / 100000000000000 : ℝ))
      (E := (cell12779 ⟨19, by decide⟩).energy) (xi := (66392646708037 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12779 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12779]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12779])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12779) (a := (41707489434869 / 50000000000000 : ℝ)) (b := (4029364601 / 2500000000000 : ℝ)) (q := (2241953528373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12779])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12779]

theorem cert12780_0 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (84074787660851 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (280219673911 / 12500000000000 : ℝ))
      (E := (cell12780 ⟨0, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (84074787660851 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (280219673911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_1 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (21009959535983 / 25000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (280220170403 / 12500000000000 : ℝ))
      (E := (cell12780 ⟨1, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (21009959535983 / 25000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (280220170403 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_2 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (4200245676263 / 5000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120882681499 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨2, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (4200245676263 / 5000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120882681499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_3 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83970013768413 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241769399377 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨3, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83970013768413 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241769399377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_4 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (2098378470929 / 2500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120886682523 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨4, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (2098378470929 / 2500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120886682523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_5 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41950144347731 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448355476797 / 20000000000000 : ℝ))
      (E := (cell12780 ⟨5, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41950144347731 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448355476797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_6 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83865463307467 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120890703117 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨6, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83865463307467 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120890703117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_7 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41915331318757 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241785381481 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨7, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41915331318757 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241785381481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_8 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (5237242915633 / 6250000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120894687539 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨8, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (5237242915633 / 6250000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120894687539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_9 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83761135310017 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (140112087137 / 6250000000000 : ℝ))
      (E := (cell12780 ⟨9, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83761135310017 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (140112087137 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_10 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83726408582077 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448359477537 / 20000000000000 : ℝ))
      (E := (cell12780 ⟨10, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83726408582077 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (448359477537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_11 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (10461463303923 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241801420229 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨11, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (10461463303923 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241801420229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_12 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83657028823199 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241805382041 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨12, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83657028823199 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241805382041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_13 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83622375722963 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (35028271803 / 1562500000000 : ℝ))
      (E := (cell12780 ⟨13, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83622375722963 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (35028271803 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_14 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (41793873548147 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241813408061 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨14, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (41793873548147 / 50000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241813408061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_15 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (1305517857953 / 1562500000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120908712827 / 50000000000000 : ℝ))
      (E := (cell12780 ⟨15, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (1305517857953 / 1562500000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (1120908712827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_16 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83518563127033 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (112091069767 / 5000000000000 : ℝ))
      (E := (cell12780 ⟨16, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83518563127033 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (112091069767 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_17 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (83484007716569 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241825380383 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨17, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (83484007716569 / 100000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241825380383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_18 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (10431184580491 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (112091469283 / 5000000000000 : ℝ))
      (E := (cell12780 ⟨18, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (10431184580491 / 12500000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (112091469283 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12780_19 : CellCertificate 12780 (884469040950859 / 10000000000000000 : ℝ) (821767819754597 / 500000000000000000 : ℝ) (41492079136243 / 1250000000000000 : ℝ)
    (cell12780 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · norm_num [cell12780]
  · have h := gap_lower (n := 12780) (a := (8341496987561 / 10000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241833415809 / 100000000000000 : ℝ))
      (E := (cell12780 ⟨19, by decide⟩).energy) (xi := (41492079136243 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12780 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12780]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12780])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12780) (a := (8341496987561 / 10000000000000 : ℝ)) (b := (40290455197 / 25000000000000 : ℝ)) (q := (2241833415809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12780])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12780]

theorem cert12781_0 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (84074772721813 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241637249847 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨0, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (84074772721813 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241637249847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_1 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (84039823521853 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (44832824999 / 2000000000000 : ℝ))
      (E := (cell12781 ⟨1, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (84039823521853 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (44832824999 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_2 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (84004899219691 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120822639331 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨2, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (84004899219691 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120822639331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_3 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83969999778907 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120824643429 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨3, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83969999778907 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120824643429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_4 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83935125163271 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241653282977 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨4, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83935125163271 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241653282977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_5 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (16780055067349 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120828637599 / 50000000000000 : ℝ))
      (E := (cell12781 ⟨5, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (16780055067349 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (1120828637599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_6 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83865450263479 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241661271447 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨6, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83865450263479 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241661271447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_7 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83830649907811 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (448333055879 / 20000000000000 : ℝ))
      (E := (cell12781 ⟨7, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83830649907811 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (448333055879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_8 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83795874234267 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241669248451 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨8, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83795874234267 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241669248451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_9 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (41880561603779 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241673301769 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨9, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (41880561603779 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241673301769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_10 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83726396792579 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241677272177 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨10, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83726396792579 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241677272177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_11 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83691694954409 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560420320587 / 25000000000000 : ℝ))
      (E := (cell12781 ⟨11, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83691694954409 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (560420320587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_12 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (20914254414577 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (11208426403 / 500000000000 : ℝ))
      (E := (cell12781 ⟨12, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (20914254414577 / 25000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (11208426403 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_13 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83622364869717 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (224168927303 / 10000000000000 : ℝ))
      (E := (cell12781 ⟨13, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83622364869717 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (224168927303 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_14 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (41793868277129 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140105829093 / 6250000000000 : ℝ))
      (E := (cell12781 ⟨14, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (41793868277129 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140105829093 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_15 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (8355313267773 / 10000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241697263581 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨15, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (8355313267773 / 10000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241697263581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_16 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (8351855320611 / 10000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (224170127267 / 10000000000000 : ℝ))
      (E := (cell12781 ⟨16, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (8351855320611 / 10000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (224170127267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_17 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (83483998105551 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140106581117 / 6250000000000 : ℝ))
      (E := (cell12781 ⟨17, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (83483998105551 / 100000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (140106581117 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_18 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (41724733671191 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (35026707591 / 1562500000000 : ℝ))
      (E := (cell12781 ⟨18, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (41724733671191 / 50000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (35026707591 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12781_19 : CellCertificate 12781 (884441441037843 / 10000000000000000 : ℝ) (82170350269821 / 50000000000000000 : ℝ) (331910036954763 / 10000000000000000 : ℝ)
    (cell12781 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · norm_num [cell12781]
  · have h := gap_lower (n := 12781) (a := (16682992176621 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241713299353 / 100000000000000 : ℝ))
      (E := (cell12781 ⟨19, by decide⟩).energy) (xi := (331910036954763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12781 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12781]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12781])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12781) (a := (16682992176621 / 20000000000000 : ℝ)) (b := (16114905957 / 10000000000000 : ℝ)) (q := (2241713299353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12781])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12781]

theorem cert12782_0 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (21018689446279 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241517161597 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨0, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (21018689446279 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241517161597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_1 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (3361592356083 / 4000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560380297483 / 25000000000000 : ℝ))
      (E := (cell12782 ⟨1, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (3361592356083 / 4000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (560380297483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_2 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (42002442458193 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241525189777 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨2, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (42002442458193 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241525189777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_3 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83969985791627 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (224152916983 / 10000000000000 : ℝ))
      (E := (cell12782 ⟨3, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83969985791627 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (224152916983 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_4 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (8393511149157 / 10000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120766598219 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨4, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (8393511149157 / 10000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120766598219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_5 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41950130990089 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448307443983 / 20000000000000 : ℝ))
      (E := (cell12782 ⟨5, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41950130990089 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448307443983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_6 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41932718610801 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241541190227 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨6, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41932718610801 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241541190227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_7 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41915318590091 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120772586477 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨7, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41915318590091 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120772586477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_8 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83795861820443 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120774587757 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨8, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83795861820443 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120774587757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_9 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83761111107097 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241553205071 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨9, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83761111107097 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241553205071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_10 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41863192502521 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241557210483 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨10, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41863192502521 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241557210483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_11 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (20922920869839 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448312239669 / 20000000000000 : ℝ))
      (E := (cell12782 ⟨11, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (20922920869839 / 25000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (448312239669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_12 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (836570064953 / 1000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241565175001 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨12, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (836570064953 / 1000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241565175001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_13 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41811177009159 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241569204669 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨13, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41811177009159 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241569204669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_14 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83587726014031 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (17932585881 / 800000000000 : ℝ))
      (E := (cell12782 ⟨14, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83587726014031 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (17932585881 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_15 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (1044414030603 / 1250000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120788606901 / 50000000000000 : ℝ))
      (E := (cell12782 ⟨15, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (1044414030603 / 1250000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1120788606901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_16 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83518543286921 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241581204187 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨16, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83518543286921 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241581204187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_17 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (83483988496231 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1094524029 / 48828125000 : ℝ))
      (E := (cell12782 ⟨17, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (83483988496231 / 100000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (1094524029 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_18 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (651948890957 / 781250000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241589240297 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨18, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (651948890957 / 781250000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241589240297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12782_19 : CellCertificate 12782 (884413845268741 / 10000000000000000 : ℝ) (410819597854401 / 250000000000000000 : ℝ) (331883445133511 / 10000000000000000 : ℝ)
    (cell12782 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · norm_num [cell12782]
  · have h := gap_lower (n := 12782) (a := (41707475946111 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241593237269 / 100000000000000 : ℝ))
      (E := (cell12782 ⟨19, by decide⟩).energy) (xi := (331883445133511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12782 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12782]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12782])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12782) (a := (41707475946111 / 50000000000000 : ℝ)) (b := (80568150193 / 50000000000000 : ℝ)) (q := (2241593237269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12782])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12782]

theorem cert12783_0 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (84074742850759 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (112069856327 / 5000000000000 : ℝ))
      (E := (cell12783 ⟨0, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (84074742850759 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (112069856327 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_1 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (420198971423 / 500000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (89656045013 / 4000000000000 : ℝ))
      (E := (cell12783 ⟨1, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (420198971423 / 500000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (89656045013 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_2 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (5250304413459 / 6250000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241405154211 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨2, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (5250304413459 / 6250000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241405154211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_3 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (20992492951643 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241409164071 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨3, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (20992492951643 / 25000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241409164071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_4 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83935097822057 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120706581671 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨4, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83935097822057 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120706581671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_5 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83900248625761 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120708580101 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨5, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83900248625761 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120708580101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_6 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83865424181837 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120710581287 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨6, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83865424181837 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120710581287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_7 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (670644995637 / 800000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120712560073 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨7, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (670644995637 / 800000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120712560073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_8 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83795849408653 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241429156271 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨8, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83795849408653 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241429156271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_9 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41880549504317 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120716581063 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨9, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41880549504317 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120716581063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_10 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (10465796652433 / 12500000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120718572277 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨10, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (10465796652433 / 12500000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120718572277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_11 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (5230729500389 / 6250000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241441168221 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨11, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (5230729500389 / 6250000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241441168221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_12 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83656995334177 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120722561671 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨12, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83656995334177 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120722561671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_13 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41811171584383 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241449132189 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨13, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41811171584383 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241449132189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_14 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83587715475613 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120726571267 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨14, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83587715475613 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120726571267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_15 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83553112220521 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120728579991 / 50000000000000 : ℝ))
      (E := (cell12783 ⟨15, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83553112220521 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (1120728579991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_16 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83518533369467 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241461131699 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨16, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83518533369467 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241461131699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_17 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (41741989444303 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (448293035833 / 20000000000000 : ℝ))
      (E := (cell12783 ⟨17, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (41741989444303 / 50000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (448293035833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_18 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (8344944874427 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241469190843 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨18, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (8344944874427 / 10000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241469190843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12783_19 : CellCertificate 12783 (35375450145703 / 400000000000000 : ℝ) (1643149797568019 / 1000000000000000000 : ℝ) (82964214406263 / 2500000000000000 : ℝ)
    (cell12783 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · norm_num [cell12783]
  · have h := gap_lower (n := 12783) (a := (83414942902961 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241473171297 / 100000000000000 : ℝ))
      (E := (cell12783 ⟨19, by decide⟩).energy) (xi := (82964214406263 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12783 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12783]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12783])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12783) (a := (83414942902961 / 100000000000000 : ℝ)) (b := (32224708647 / 20000000000000 : ℝ)) (q := (2241473171297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12783])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12783]

theorem cert12784_0 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (84074727918741 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (112063854343 / 5000000000000 : ℝ))
      (E := (cell12784 ⟨0, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (84074727918741 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (112063854343 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_1 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (42019889834713 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241281113977 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨1, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (42019889834713 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241281113977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_2 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (16800971263313 / 20000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241285114099 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨2, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (16800971263313 / 20000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241285114099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_3 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41984978911871 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241289095917 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨3, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41984978911871 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241289095917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_4 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83935084154729 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (112064656289 / 5000000000000 : ℝ))
      (E := (cell12784 ⟨4, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83935084154729 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (112064656289 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_5 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83900235273491 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120648548031 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨5, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83900235273491 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120648548031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_6 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83865411144181 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120650565267 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨6, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83865411144181 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120650565267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_7 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83830611731141 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241305120969 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨7, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83830611731141 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241305120969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_8 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41897918499449 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241309132717 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨8, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41897918499449 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241309132717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_9 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83761086912167 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (224131311491 / 10000000000000 : ℝ))
      (E := (cell12784 ⟨9, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83761086912167 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (224131311491 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_10 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (16745272287169 / 20000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560329283111 / 25000000000000 : ℝ))
      (E := (cell12784 ⟨10, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (16745272287169 / 20000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560329283111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_11 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41845830267507 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120660566951 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨11, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41845830267507 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120660566951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_12 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41828492087469 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120662562813 / 50000000000000 : ℝ))
      (E := (cell12784 ⟨12, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41828492087469 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (1120662562813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_13 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (4181116616053 / 5000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241329113713 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨13, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (4181116616053 / 5000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241329113713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_14 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (20896926234751 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560333290539 / 25000000000000 : ℝ))
      (E := (cell12784 ⟨14, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (20896926234751 / 25000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (560333290539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_15 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (83553101994573 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (224133716029 / 10000000000000 : ℝ))
      (E := (cell12784 ⟨15, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (83553101994573 / 100000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (224133716029 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_16 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (16703704690749 / 20000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241341113403 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨16, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (16703704690749 / 20000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241341113403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_17 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41741984641339 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241345142973 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨17, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41741984641339 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241345142973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_18 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41724719723851 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241349137463 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨18, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41724719723851 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241349137463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12784_19 : CellCertificate 12784 (884358666158367 / 10000000000000000 : ℝ) (82151061192147 / 50000000000000000 : ℝ) (165915137214127 / 5000000000000000 : ℝ)
    (cell12784 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · norm_num [cell12784]
  · have h := gap_lower (n := 12784) (a := (41707466957661 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241353159699 / 100000000000000 : ℝ))
      (E := (cell12784 ⟨19, by decide⟩).energy) (xi := (165915137214127 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12784 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12784]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12784])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12784) (a := (41707466957661 / 50000000000000 : ℝ)) (b := (40277697029 / 25000000000000 : ℝ)) (q := (2241353159699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12784])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12784]

theorem cert12785_0 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (42037356494531 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120578550187 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨0, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (42037356494531 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120578550187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_1 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (10504970632069 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560290274511 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨1, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (10504970632069 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560290274511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_2 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (84004842020049 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241165127307 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨2, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (84004842020049 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241165127307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_3 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (1312030372549 / 1562500000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448233827807 / 20000000000000 : ℝ))
      (E := (cell12785 ⟨3, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (1312030372549 / 1562500000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (448233827807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_4 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (20983767622397 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120586570831 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨4, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (20983767622397 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120586570831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_5 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (8390022192337 / 10000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560294285841 / 25000000000000 : ℝ))
      (E := (cell12785 ⟨5, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (8390022192337 / 10000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (560294285841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_6 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (20966349527159 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120590576031 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨6, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (20966349527159 / 25000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120590576031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_7 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83830599009729 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241185117441 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨7, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83830599009729 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241185117441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_8 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83795824591177 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241189104851 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨8, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83795824591177 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241189104851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_9 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (2617533588053 / 3125000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241193121451 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨9, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (2617533588053 / 3125000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241193121451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_10 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (16745269930837 / 20000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241197116099 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨10, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (16745269930837 / 20000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241197116099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_11 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (3347665962629 / 4000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241201153463 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨11, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (3347665962629 / 4000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241201153463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_12 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83656973017581 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120602561877 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨12, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83656973017581 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120602561877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_13 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83622321475199 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120604574621 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨13, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83622321475199 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120604574621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_14 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41793847202101 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241213119553 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨14, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41793847202101 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241213119553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_15 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (16710618354079 / 20000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241217156557 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨15, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (16710618354079 / 20000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241217156557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_16 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83518513539757 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (140076321831 / 6250000000000 : ℝ))
      (E := (cell12785 ⟨16, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83518513539757 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (140076321831 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_17 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (41741979839223 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241225161031 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨17, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (41741979839223 / 50000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241225161031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_18 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (10431178769099 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241229138397 / 100000000000000 : ℝ))
      (E := (cell12785 ⟨18, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (10431178769099 / 12500000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (2241229138397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12785_19 : CellCertificate 12785 (884331082815139 / 10000000000000000 : ℝ) (821446335118821 / 500000000000000000 : ℝ) (165901847770993 / 5000000000000000 : ℝ)
    (cell12785 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · norm_num [cell12785]
  · have h := gap_lower (n := 12785) (a := (83414924929303 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120616572107 / 50000000000000 : ℝ))
      (E := (cell12785 ⟨19, by decide⟩).energy) (xi := (165901847770993 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12785 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12785]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12785])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12785) (a := (83414924929303 / 100000000000000 : ℝ)) (b := (16109803503 / 10000000000000 : ℝ)) (q := (1120616572107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12785])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12785]

theorem cert12786_0 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (42037349030861 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (448207433417 / 20000000000000 : ℝ))
      (E := (cell12786 ⟨0, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (42037349030861 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (448207433417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_1 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (42019875222989 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241041135371 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨1, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (42019875222989 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241041135371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_2 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (42002413862897 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560261283993 / 25000000000000 : ℝ))
      (E := (cell12786 ⟨2, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (42002413862897 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560261283993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_3 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41984964932377 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241049177649 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨3, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41984964932377 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241049177649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_4 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (10491882103329 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241053153079 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨4, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (10491882103329 / 12500000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241053153079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_5 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (20975052143849 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (7003303707 / 312500000000 : ℝ))
      (E := (cell12786 ⟨5, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (20975052143849 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (7003303707 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_6 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (6551983209 / 7812500000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560265292301 / 25000000000000 : ℝ))
      (E := (cell12786 ⟨6, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (6551983209 / 7812500000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560265292301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_7 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (20957646572597 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241065167549 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨7, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (20957646572597 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241065167549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_8 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (8379581218549 / 10000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241069188687 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨8, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (8379581218549 / 10000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241069188687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_9 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83761062725221 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (8964292727 / 400000000000 : ℝ))
      (E := (cell12786 ⟨9, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83761062725221 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (8964292727 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_10 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41863168937241 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (280134644197 / 12500000000000 : ℝ))
      (E := (cell12786 ⟨10, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41863168937241 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (280134644197 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_11 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (20922909399589 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241081168831 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨11, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (20922909399589 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241081168831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_12 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (20914240465527 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120542587913 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨12, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (20914240465527 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120542587913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_13 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83622310631183 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (140068073791 / 6250000000000 : ℝ))
      (E := (cell12786 ⟨13, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83622310631183 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (140068073791 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_14 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83587683871209 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560273297291 / 25000000000000 : ℝ))
      (E := (cell12786 ⟨14, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83587683871209 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (560273297291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_15 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83553081547987 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (448219441391 / 20000000000000 : ℝ))
      (E := (cell12786 ⟨15, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83553081547987 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (448219441391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_16 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (41759251813751 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241101181189 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨16, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (41759251813751 / 50000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241101181189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_17 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (20870987518977 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241105175129 / 100000000000000 : ℝ))
      (E := (cell12786 ⟨17, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (20870987518977 / 25000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (2241105175129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_18 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (83449420859541 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (448221838729 / 20000000000000 : ℝ))
      (E := (cell12786 ⟨18, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (83449420859541 / 100000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (448221838729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12786_19 : CellCertificate 12786 (884303503611913 / 10000000000000000 : ℝ) (410691034186851 / 250000000000000000 : ℝ) (82944280241279 / 2500000000000000 : ℝ)
    (cell12786 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · norm_num [cell12786]
  · have h := gap_lower (n := 12786) (a := (16682983188981 / 20000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120556591553 / 50000000000000 : ℝ))
      (E := (cell12786 ⟨19, by decide⟩).energy) (xi := (82944280241279 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12786 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12786]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12786])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12786) (a := (16682983188981 / 20000000000000 : ℝ)) (b := (6443411359 / 4000000000000 : ℝ)) (q := (1120556591553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12786])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12786]

theorem cert12787_0 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (84074683136719 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (280114653647 / 12500000000000 : ℝ))
      (E := (cell12787 ⟨0, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (84074683136719 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (280114653647 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_1 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (10504966979713 / 12500000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240921225959 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨1, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (10504966979713 / 12500000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240921225959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_2 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (84004813433801 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120462627913 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨2, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (84004813433801 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120462627913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_3 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (16793983177719 / 20000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240929211759 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨3, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (16793983177719 / 20000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240929211759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_4 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41967521582931 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (280116652243 / 12500000000000 : ℝ))
      (E := (cell12787 ⟨4, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41967521582931 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (280116652243 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_5 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83900195229569 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560234306173 / 25000000000000 : ℝ))
      (E := (cell12787 ⟨5, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83900195229569 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560234306173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_6 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41932686021937 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120470619959 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨6, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41932686021937 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120470619959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_7 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83830573573119 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240945213309 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨7, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83830573573119 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240945213309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_8 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (20948949945459 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448189853643 / 20000000000000 : ℝ))
      (E := (cell12787 ⟨8, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (20948949945459 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (448189853643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_9 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41880525317371 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240953237779 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨9, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41880525317371 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240953237779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_10 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83726326096737 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (17927657959 / 800000000000 : ℝ))
      (E := (cell12787 ⟨10, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83726326096737 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (17927657959 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_11 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83691626132907 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240961238083 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨11, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83691626132907 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240961238083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_12 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (20914237677129 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120482611873 / 50000000000000 : ℝ))
      (E := (cell12787 ⟨12, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (20914237677129 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (1120482611873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_13 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (20905574947253 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240969266077 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨13, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (20905574947253 / 25000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240969266077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_14 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41793836670011 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240973254699 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨14, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41793836670011 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240973254699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_15 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (1671061426547 / 2000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240977253313 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨15, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (1671061426547 / 2000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240977253313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_16 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41759246858489 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560245316819 / 25000000000000 : ℝ))
      (E := (cell12787 ⟨16, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41759246858489 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (560245316819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_17 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (41741970237533 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240985243481 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨17, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (41741970237533 / 50000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240985243481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_18 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (83449411567947 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240989244971 / 100000000000000 : ℝ))
      (E := (cell12787 ⟨18, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (83449411567947 / 100000000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (2240989244971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12787_19 : CellCertificate 12787 (442137964273857 / 5000000000000000 : ℝ) (328527124673501 / 200000000000000000 : ℝ) (5183602354633 / 156250000000000 : ℝ)
    (cell12787 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · norm_num [cell12787]
  · have h := gap_lower (n := 12787) (a := (5213431685133 / 6250000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (280124159547 / 12500000000000 : ℝ))
      (E := (cell12787 ⟨19, by decide⟩).energy) (xi := (5183602354633 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12787 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12787]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12787])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12787) (a := (5213431685133 / 6250000000000 : ℝ)) (b := (161072534951 / 100000000000000 : ℝ)) (q := (280124159547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12787])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12787]

theorem cert12788_0 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (42037334107027 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448159468893 / 20000000000000 : ℝ))
      (E := (cell12788 ⟨0, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (42037334107027 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448159468893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_1 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (84039721231729 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120400655983 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨1, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (84039721231729 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120400655983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_2 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (21001199786017 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240805313273 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨2, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (21001199786017 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240805313273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_3 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41984950957329 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120404678573 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨3, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41984950957329 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120404678573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_4 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (20983757376819 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240813336259 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨4, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (20983757376819 / 25000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240813336259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_5 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83900181885889 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120408658327 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨5, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83900181885889 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120408658327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_6 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (16773071802931 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (140051335263 / 6250000000000 : ℝ))
      (E := (cell12788 ⟨6, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (16773071802931 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (140051335263 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_7 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (261970502681 / 312500000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448165062541 / 20000000000000 : ℝ))
      (E := (cell12788 ⟨7, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (261970502681 / 312500000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448165062541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_8 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (16759157476043 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560207335859 / 25000000000000 : ℝ))
      (E := (cell12788 ⟨8, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (16759157476043 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560207335859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_9 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83761038546257 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (224083334757 / 10000000000000 : ℝ))
      (E := (cell12788 ⟨9, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83761038546257 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (224083334757 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_10 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (1674526286419 / 2000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240837331943 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨10, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (1674526286419 / 2000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240837331943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_11 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83691614669377 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240841361221 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨11, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83691614669377 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240841361221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_12 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41828469778403 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560211331403 / 25000000000000 : ℝ))
      (E := (cell12788 ⟨12, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41828469778403 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (560211331403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_13 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (16724457789737 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (280106168423 / 12500000000000 : ℝ))
      (E := (cell12788 ⟨13, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (16724457789737 / 20000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (280106168423 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_14 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41793831405321 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (70026667947 / 3125000000000 : ℝ))
      (E := (cell12788 ⟨14, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41793831405321 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (70026667947 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_15 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83553061108481 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448171470761 / 20000000000000 : ℝ))
      (E := (cell12788 ⟨15, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83553061108481 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448171470761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_16 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (83518483808187 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120430674681 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨16, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (83518483808187 / 100000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120430674681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_17 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (41741965437959 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240865366089 / 100000000000000 : ℝ))
      (E := (cell12788 ⟨17, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (41741965437959 / 50000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (2240865366089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_18 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (8344940227801 / 10000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448173870123 / 20000000000000 : ℝ))
      (E := (cell12788 ⟨18, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (8344940227801 / 10000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (448173870123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12788_19 : CellCertificate 12788 (884248357621563 / 10000000000000000 : ℝ) (821253565046613 / 500000000000000000 : ℝ) (66344796947009 / 2000000000000000 : ℝ)
    (cell12788 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · norm_num [cell12788]
  · have h := gap_lower (n := 12788) (a := (8341489798097 / 10000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120436682881 / 50000000000000 : ℝ))
      (E := (cell12788 ⟨19, by decide⟩).energy) (xi := (66344796947009 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12788 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12788]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12788])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12788) (a := (8341489798097 / 10000000000000 : ℝ)) (b := (80529893979 / 50000000000000 : ℝ)) (q := (1120436682881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12788])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12788]

theorem cert12789_0 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (3362986131749 / 4000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120338727569 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨0, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (3362986131749 / 4000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120338727569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_1 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (21009926657013 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240681451237 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨1, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (21009926657013 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240681451237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_2 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (21001196214149 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240685481913 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨2, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (21001196214149 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240685481913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_3 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (2624058998217 / 3125000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240689440143 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨3, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (2624058998217 / 3125000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240689440143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_4 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83935015850873 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120346725057 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨4, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83935015850873 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120346725057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_5 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41950084272177 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240697462131 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨5, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41950084272177 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240697462131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_6 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (16773069197509 / 20000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240701484113 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨6, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (16773069197509 / 20000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240701484113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_7 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83830548144791 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (112035273287 / 5000000000000 : ℝ))
      (E := (cell12789 ⟨7, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83830548144791 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (112035273287 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_8 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41897887490313 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240709472357 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨8, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41897887490313 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240709472357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_9 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83761026459767 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240713453093 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨9, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83761026459767 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240713453093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_10 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83726302547119 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560179368209 / 25000000000000 : ℝ))
      (E := (cell12789 ⟨10, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83726302547119 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560179368209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_11 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83691603207767 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (280090185021 / 12500000000000 : ℝ))
      (E := (cell12789 ⟨11, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83691603207767 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (280090185021 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_12 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41828464203489 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240725481427 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨12, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41828464203489 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240725481427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_13 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41811139055101 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120364741351 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨13, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41811139055101 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120364741351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_14 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (20896913070767 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560183372459 / 25000000000000 : ℝ))
      (E := (cell12789 ⟨14, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (20896913070767 / 25000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (560183372459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_15 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83553050891381 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240737508431 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨15, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83553050891381 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240737508431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_16 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (41759236950563 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120370742823 / 50000000000000 : ℝ))
      (E := (cell12789 ⟨16, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (41759236950563 / 50000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (1120370742823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_17 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (163054533747 / 195312500000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240745484739 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨17, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (163054533747 / 195312500000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240745484739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_18 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (83449392989729 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240749510579 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨18, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (83449392989729 / 100000000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240749510579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12789_19 : CellCertificate 12789 (176844158166497 / 2000000000000000 : ℝ) (1642378656919849 / 1000000000000000000 : ℝ) (331697423079583 / 10000000000000000 : ℝ)
    (cell12789 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · norm_num [cell12789]
  · have h := gap_lower (n := 12789) (a := (10426861125179 / 12500000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240753509529 / 100000000000000 : ℝ))
      (E := (cell12789 ⟨19, by decide⟩).energy) (xi := (331697423079583 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12789 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12789]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12789])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12789) (a := (10426861125179 / 12500000000000 : ℝ)) (b := (80523521497 / 50000000000000 : ℝ)) (q := (2240753509529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12789])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12789]

theorem cert12790_0 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (21018659593933 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240557619011 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨0, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (21018659593933 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240557619011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_1 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (84039692026673 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560140410943 / 25000000000000 : ℝ))
      (E := (cell12790 ⟨1, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (84039692026673 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560140410943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_2 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (84004770571383 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560141411503 / 25000000000000 : ℝ))
      (E := (cell12790 ⟨2, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (84004770571383 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (560141411503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_3 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83969873973451 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240569634417 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨3, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83969873973451 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240569634417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_4 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16787000439331 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120286808709 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨4, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16787000439331 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120286808709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_5 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (16780031040993 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (448115520637 / 20000000000000 : ℝ))
      (E := (cell12790 ⟨5, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (16780031040993 / 20000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (448115520637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_6 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41932666481271 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120290828797 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨6, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41932666481271 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120290828797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_7 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (20957633858433 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240585614429 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨7, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (20957633858433 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240585614429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_8 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (20948940645767 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120294827489 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨8, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (20948940645767 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120294827489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_9 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83761014375271 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120296806189 / 50000000000000 : ℝ))
      (E := (cell12790 ⟨9, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83761014375271 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (1120296806189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_10 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (20931572693811 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240597609501 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨10, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (20931572693811 / 25000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240597609501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_11 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41845795874037 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240601653003 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨11, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41845795874037 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240601653003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_12 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83656917259031 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240605633089 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨12, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83656917259031 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240605633089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_13 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83622267273563 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240609672029 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨13, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83622267273563 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240609672029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_14 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (835876417573 / 1000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (28007670743 / 1250000000000 : ℝ))
      (E := (cell12790 ⟨14, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (835876417573 / 1000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (28007670743 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_15 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83553040676049 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240617659021 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨15, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83553040676049 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240617659021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_16 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83518463995797 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (17924973409 / 800000000000 : ℝ))
      (E := (cell12790 ⟨16, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83518463995797 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (17924973409 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_17 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (5217744480169 / 6250000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (448125131529 / 20000000000000 : ℝ))
      (E := (cell12790 ⟨17, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (5217744480169 / 6250000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (448125131529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_18 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (41724691851553 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240629666619 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨18, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (41724691851553 / 50000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240629666619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12790_19 : CellCertificate 12790 (55262076761219 / 625000000000000 : ℝ) (51320318870083 / 31250000000000000 : ℝ) (331670865728997 / 10000000000000000 : ℝ)
    (cell12790 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · norm_num [cell12790]
  · have h := gap_lower (n := 12790) (a := (83414880023513 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240633649413 / 100000000000000 : ℝ))
      (E := (cell12790 ⟨19, by decide⟩).energy) (xi := (331670865728997 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12790 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12790]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12790])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12790) (a := (83414880023513 / 100000000000000 : ℝ)) (b := (161034300061 / 100000000000000 : ℝ)) (q := (2240633649413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12790])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12790]

theorem cert12791_0 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (3362984938403 / 4000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (280054729511 / 12500000000000 : ℝ))
      (E := (cell12791 ⟨0, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (3362984938403 / 4000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (280054729511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_1 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (84039677427591 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240441831731 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨1, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (84039677427591 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240441831731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_2 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (8400475628843 / 10000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120222902787 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨2, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (8400475628843 / 10000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120222902787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_3 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83969860006179 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120224912097 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨3, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83969860006179 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120224912097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_4 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83934988544619 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240453838177 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨4, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83934988544619 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240453838177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_5 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83900141867721 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448091559551 / 20000000000000 : ℝ))
      (E := (cell12791 ⟨5, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83900141867721 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448091559551 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_6 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41932659969823 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448092365339 / 20000000000000 : ℝ))
      (E := (cell12791 ⟨6, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41932659969823 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448092365339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_7 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83830522724741 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240465816761 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨7, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83830522724741 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240465816761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_8 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41897875093771 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140029364581 / 6250000000000 : ℝ))
      (E := (cell12791 ⟨8, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41897875093771 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140029364581 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_9 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (2617531321649 / 3125000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240473825429 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨9, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (2617531321649 / 3125000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240473825429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_10 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (3349051160213 / 4000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240477799993 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨10, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (3349051160213 / 4000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240477799993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_11 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (836915802903 / 1000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240481821649 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨11, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (836915802903 / 1000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240481821649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_12 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (20914226528241 / 25000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140030364919 / 6250000000000 : ℝ))
      (E := (cell12791 ⟨12, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (20914226528241 / 25000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (140030364919 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_13 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41811128219383 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120244928623 / 50000000000000 : ℝ))
      (E := (cell12791 ⟨13, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41811128219383 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (1120244928623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_14 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83587631233337 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (560123456243 / 25000000000000 : ℝ))
      (E := (cell12791 ⟨14, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83587631233337 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (560123456243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_15 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41776515231243 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (560124465937 / 25000000000000 : ℝ))
      (E := (cell12791 ⟨15, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41776515231243 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (560124465937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_16 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (41759227046099 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240501862609 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨16, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (41759227046099 / 50000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240501862609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_17 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (20870975522159 / 25000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448101165319 / 20000000000000 : ℝ))
      (E := (cell12791 ⟨17, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (20870975522159 / 25000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (448101165319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_18 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83449374418137 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240509818743 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨18, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83449374418137 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240509818743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12791_19 : CellCertificate 12791 (884165669661643 / 10000000000000000 : ℝ) (821060885428467 / 500000000000000000 : ℝ) (331644312682159 / 10000000000000000 : ℝ)
    (cell12791 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · norm_num [cell12791]
  · have h := gap_lower (n := 12791) (a := (83414871047213 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240513843679 / 100000000000000 : ℝ))
      (E := (cell12791 ⟨19, by decide⟩).energy) (xi := (331644312682159 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12791 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12791]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12791])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12791) (a := (83414871047213 / 100000000000000 : ℝ)) (b := (40255389789 / 25000000000000 : ℝ)) (q := (2240513843679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12791])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12791]

theorem cert12792_0 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (84074608546753 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240318048549 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨0, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (84074608546753 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240318048549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_1 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (42019831415403 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240322015113 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨1, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (42019831415403 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240322015113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_2 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (16800948401547 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120163009233 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨2, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (16800948401547 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120163009233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_3 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83969846041127 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560082516841 / 25000000000000 : ℝ))
      (E := (cell12792 ⟨3, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83969846041127 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560082516841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_4 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (16786994978953 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240334054477 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨4, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (16786994978953 / 20000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240334054477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_5 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41950064266311 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240338045841 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨5, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41950064266311 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240338045841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_6 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83865306918857 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240342049373 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨6, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83865306918857 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240342049373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_7 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (4191525500891 / 5000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560086518183 / 25000000000000 : ℝ))
      (E := (cell12792 ⟨7, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (4191525500891 / 5000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560086518183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_8 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41897868897023 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120175032659 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨8, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41897868897023 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120175032659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_9 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41880495106129 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (280044254277 / 12500000000000 : ℝ))
      (E := (cell12792 ⟨9, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41880495106129 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (280044254277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_10 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83726267237361 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (280044755539 / 12500000000000 : ℝ))
      (E := (cell12792 ⟨10, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83726267237361 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (280044755539 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_11 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83691568834443 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120181022093 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨11, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83691568834443 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120181022093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_12 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (10457111871097 / 12500000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (224036604017 / 10000000000000 : ℝ))
      (E := (cell12792 ⟨12, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (10457111871097 / 12500000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (224036604017 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_13 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83622245605811 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120185019177 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨13, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83622245605811 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120185019177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_14 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83587620711179 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240374044579 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨14, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83587620711179 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240374044579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_15 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83553020250689 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120189032221 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨15, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83553020250689 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120189032221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_16 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (83518444190329 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120191022549 / 50000000000000 : ℝ))
      (E := (cell12792 ⟨16, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (83518444190329 / 100000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (1120191022549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_17 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (41741946248131 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560096512451 / 25000000000000 : ℝ))
      (E := (cell12792 ⟨17, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (41741946248131 / 50000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560096512451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_18 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (3337974605393 / 4000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560097520857 / 25000000000000 : ℝ))
      (E := (cell12792 ⟨18, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (3337974605393 / 4000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (560097520857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12792_19 : CellCertificate 12792 (110517264409741 / 1250000000000000 : ℝ) (164199335795797 / 100000000000000000 : ℝ) (331617763937939 / 10000000000000000 : ℝ)
    (cell12792 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · norm_num [cell12792]
  · have h := gap_lower (n := 12792) (a := (8341486207253 / 10000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240394092331 / 100000000000000 : ℝ))
      (E := (cell12792 ⟨19, by decide⟩).energy) (xi := (331617763937939 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12792 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12792]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12792])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12792) (a := (8341486207253 / 10000000000000 : ℝ)) (b := (4025220507 / 2500000000000 : ℝ)) (q := (2240394092331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12792])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12792]

theorem cert12793_0 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (16814918727153 / 20000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240198314217 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨0, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (16814918727153 / 20000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240198314217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_1 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (42019824118159 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120101154803 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨1, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (42019824118159 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120101154803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_2 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (42002363864649 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (140012892793 / 6250000000000 : ℝ))
      (E := (cell12793 ⟨2, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (42002363864649 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (140012892793 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_3 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (10496229009787 / 12500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560052576509 / 25000000000000 : ℝ))
      (E := (cell12793 ⟨3, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (10496229009787 / 12500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560052576509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_4 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41967480623547 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240214266319 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨4, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41967480623547 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240214266319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_5 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41950057599833 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (224021828951 / 10000000000000 : ℝ))
      (E := (cell12793 ⟨5, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41950057599833 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (224021828951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_6 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83865293900173 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240222267673 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨6, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83865293900173 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240222267673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_7 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41915248656483 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240226324363 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨7, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41915248656483 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240226324363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_8 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83795725402581 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240230293037 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨8, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83795725402581 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240230293037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_9 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83760978133741 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (35003660887 / 1562500000000 : ℝ))
      (E := (cell12793 ⟨9, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83760978133741 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (35003660887 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_10 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (10465781933919 / 12500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240238284407 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨10, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (10465781933919 / 12500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240238284407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_11 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (10461444672563 / 12500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560060580153 / 25000000000000 : ℝ))
      (E := (cell12793 ⟨11, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (10461444672563 / 12500000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560060580153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_12 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83656883826469 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560061573897 / 25000000000000 : ℝ))
      (E := (cell12793 ⟨12, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83656883826469 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560061573897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_13 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83622234774699 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240250331599 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨13, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83622234774699 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240250331599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_14 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41793805095413 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120127159131 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨14, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41793805095413 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120127159131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_15 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (4177650502033 / 5000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240258319273 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨15, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (4177650502033 / 5000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240258319273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_16 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (8351843429019 / 10000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240262339981 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨16, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (8351843429019 / 10000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240262339981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_17 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (4174194145279 / 5000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560066581819 / 25000000000000 : ℝ))
      (E := (cell12793 ⟨17, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (4174194145279 / 5000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (560066581819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_18 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (83449355853167 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240270344197 / 100000000000000 : ℝ))
      (E := (cell12793 ⟨18, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (83449355853167 / 100000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (2240270344197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12793_19 : CellCertificate 12793 (884110565027383 / 10000000000000000 : ℝ) (32837299302821 / 20000000000000000 : ℝ) (331591219495209 / 10000000000000000 : ℝ)
    (cell12793 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · norm_num [cell12793]
  · have h := gap_lower (n := 12793) (a := (41707426549733 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120137168551 / 50000000000000 : ℝ))
      (E := (cell12793 ⟨19, by decide⟩).energy) (xi := (331591219495209 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12793 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12793]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12793])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12793) (a := (41707426549733 / 50000000000000 : ℝ)) (b := (20124510429 / 12500000000000 : ℝ)) (q := (1120137168551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12793])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12793]

theorem cert12794_0 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (10509322340889 / 12500000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240078575271 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨0, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (10509322340889 / 12500000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240078575271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_1 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (672317069153 / 800000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560020635421 / 25000000000000 : ℝ))
      (E := (cell12794 ⟨1, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (672317069153 / 800000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560020635421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_2 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (42002356726559 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240086546377 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨2, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (42002356726559 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240086546377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_3 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83969818117683 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (280011324763 / 12500000000000 : ℝ))
      (E := (cell12794 ⟨3, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83969818117683 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (280011324763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_4 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (20983736900401 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560023647383 / 25000000000000 : ℝ))
      (E := (cell12794 ⟨4, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (20983736900401 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560023647383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_5 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83900101868853 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240098586699 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨5, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83900101868853 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240098586699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_6 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (16773056176719 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448020519503 / 20000000000000 : ℝ))
      (E := (cell12794 ⟨6, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (16773056176719 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448020519503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_7 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (4191524230509 / 5000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448021314331 / 20000000000000 : ℝ))
      (E := (cell12794 ⟨7, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (4191524230509 / 5000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448021314331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_8 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41897856506573 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240110574463 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨8, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41897856506573 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240110574463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_9 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (16752193211443 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240114555061 / 100000000000000 : ℝ))
      (E := (cell12794 ⟨9, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (16752193211443 / 20000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (2240114555061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_10 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83726243707297 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560029644583 / 25000000000000 : ℝ))
      (E := (cell12794 ⟨10, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83726243707297 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560029644583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_11 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83691545928481 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448024518571 / 20000000000000 : ℝ))
      (E := (cell12794 ⟨11, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83691545928481 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448024518571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_12 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (2091421817151 / 2500000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120063302481 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨12, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (2091421817151 / 2500000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120063302481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_13 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83622223945427 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448026112523 / 20000000000000 : ℝ))
      (E := (cell12794 ⟨13, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83622223945427 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448026112523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_14 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (20896899918069 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120067293939 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨14, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (20896899918069 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120067293939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_15 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (41776499916199 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120069285037 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨15, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (41776499916199 / 50000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120069285037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_16 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (4175921219589 / 5000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120071286339 / 50000000000000 : ℝ))
      (E := (cell12794 ⟨16, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (4175921219589 / 5000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (1120071286339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_17 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83483873316589 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448029320159 / 20000000000000 : ℝ))
      (E := (cell12794 ⟨17, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83483873316589 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (448029320159 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_18 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (20862336643291 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (44803012021 / 2000000000000 : ℝ))
      (E := (cell12794 ⟨18, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (20862336643291 / 25000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (44803012021 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12794_19 : CellCertificate 12794 (884083018909033 / 10000000000000000 : ℝ) (328347318480293 / 200000000000000000 : ℝ) (165782339676421 / 5000000000000000 : ℝ)
    (cell12794 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · norm_num [cell12794]
  · have h := gap_lower (n := 12794) (a := (83414844128019 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560038644499 / 25000000000000 : ℝ))
      (E := (cell12794 ⟨19, by decide⟩).energy) (xi := (165782339676421 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12794 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12794]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12794])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12794) (a := (83414844128019 / 100000000000000 : ℝ)) (b := (160983348611 / 100000000000000 : ℝ)) (q := (560038644499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12794])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12794]

theorem cert12795_0 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (84074563820791 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (447991777907 / 20000000000000 : ℝ))
      (E := (cell12795 ⟨0, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (84074563820791 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (447991777907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_1 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (84039619054227 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (17919703079 / 800000000000 : ℝ))
      (E := (cell12795 ⟨1, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (84039619054227 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (17919703079 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_2 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (21001174794799 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1119983430699 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨2, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (21001174794799 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1119983430699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_3 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (8396980415929 / 10000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (559992721419 / 25000000000000 : ℝ))
      (E := (cell12795 ⟨3, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (8396980415929 / 10000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (559992721419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_4 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (16786986791659 / 20000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2239974908289 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨4, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (16786986791659 / 20000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2239974908289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_5 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (10487511067523 / 12500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (223997887947 / 10000000000000 : ℝ))
      (E := (cell12795 ⟨5, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (10487511067523 / 12500000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (223997887947 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_6 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41932633934561 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1119991432509 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨6, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41932633934561 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1119991432509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_7 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83830471909461 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2239986872591 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨7, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83830471909461 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2239986872591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_8 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83795700625739 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (447998181919 / 20000000000000 : ℝ))
      (E := (cell12795 ⟨8, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83795700625739 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (447998181919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_9 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83760953982681 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2239994867121 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨9, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83760953982681 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2239994867121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_10 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (20931557986299 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (447999773607 / 20000000000000 : ℝ))
      (E := (cell12795 ⟨10, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (20931557986299 / 25000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (447999773607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_11 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (41845767239187 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240002918991 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨11, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (41845767239187 / 50000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240002918991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_12 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (8365686154749 / 10000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240006910189 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨12, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (8365686154749 / 10000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240006910189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_13 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83622213117997 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (224001090577 / 10000000000000 : ℝ))
      (E := (cell12795 ⟨13, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83622213117997 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (224001090577 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_14 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (8358758915553 / 10000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240014911571 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨14, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (8358758915553 / 10000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240014911571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_15 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83552989625901 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448003786637 / 20000000000000 : ℝ))
      (E := (cell12795 ⟨15, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83552989625901 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (448003786637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_16 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83518414495099 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240022917769 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨16, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83518414495099 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240022917769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_17 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (8348386372929 / 10000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (35000420759 / 1562500000000 : ℝ))
      (E := (cell12795 ⟨17, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (8348386372929 / 10000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (35000420759 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_18 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (2607791790463 / 3125000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120015456113 / 50000000000000 : ℝ))
      (E := (cell12795 ⟨18, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (2607791790463 / 3125000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (1120015456113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12795_19 : CellCertificate 12795 (884055476921903 / 10000000000000000 : ℝ) (328321647946901 / 200000000000000000 : ℝ) (33153814350971 / 1000000000000000 : ℝ)
    (cell12795 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · norm_num [cell12795]
  · have h := gap_lower (n := 12795) (a := (83414835158189 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240034931541 / 100000000000000 : ℝ))
      (E := (cell12795 ⟨19, by decide⟩).energy) (xi := (33153814350971 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12795 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12795]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12795])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12795) (a := (83414835158189 / 100000000000000 : ℝ)) (b := (80485307909 / 50000000000000 : ℝ)) (q := (2240034931541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12795])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12795]

theorem cert12796_0 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (21018637229201 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239839199187 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨0, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (21018637229201 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239839199187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_1 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (1313118819791 / 1562500000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (447968644699 / 20000000000000 : ℝ))
      (E := (cell12796 ⟨1, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (1313118819791 / 1562500000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (447968644699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_2 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (8400468490753 / 10000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119923614877 / 50000000000000 : ℝ))
      (E := (cell12796 ⟨2, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (8400468490753 / 10000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119923614877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_3 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (16793958040623 / 20000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239851226647 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨3, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (16793958040623 / 20000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239851226647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_4 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (41967460158583 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239855222593 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨4, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (41967460158583 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239855222593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_5 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83900075213657 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239859225763 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨5, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83900075213657 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239859225763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_6 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83865254856753 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119931622033 / 50000000000000 : ℝ))
      (E := (cell12796 ⟨6, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83865254856753 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119931622033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_7 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (10478807401351 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (89594689087 / 4000000000000 : ℝ))
      (E := (cell12796 ⟨7, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (10478807401351 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (89594689087 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_8 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (41897844120181 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239871240429 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨8, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (41897844120181 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239871240429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_9 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83760941910139 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239875232951 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨9, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83760941910139 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239875232951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_10 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (10465777523131 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (223987921157 / 10000000000000 : ℝ))
      (E := (cell12796 ⟨10, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (10465777523131 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (223987921157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_11 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83691523030183 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (139992702559 / 6250000000000 : ℝ))
      (E := (cell12796 ⟨11, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83691523030183 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (139992702559 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_12 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (41828425205409 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239887211273 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨12, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (41828425205409 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239887211273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_13 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (10452775286551 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239891244819 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨13, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (10452775286551 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239891244819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_14 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (20896894660147 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559973807799 / 25000000000000 : ℝ))
      (E := (cell12796 ⟨14, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (20896894660147 / 25000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559973807799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_15 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (8355297942117 / 10000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119949617049 / 50000000000000 : ℝ))
      (E := (cell12796 ⟨15, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (8355297942117 / 10000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (1119949617049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_16 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (41759202300073 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (279987907359 / 12500000000000 : ℝ))
      (E := (cell12796 ⟨16, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (41759202300073 / 50000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (279987907359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_17 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83483854143683 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559976813101 / 25000000000000 : ℝ))
      (E := (cell12796 ⟨17, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83483854143683 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (559976813101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_18 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (83449328018121 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239911277731 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨18, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (83449328018121 / 100000000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239911277731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12796_19 : CellCertificate 12796 (44201396953251 / 500000000000000 : ℝ) (205184988391933 / 125000000000000000 : ℝ) (331511611964687 / 10000000000000000 : ℝ)
    (cell12796 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · norm_num [cell12796]
  · have h := gap_lower (n := 12796) (a := (10426853273747 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239915281209 / 100000000000000 : ℝ))
      (E := (cell12796 ⟨19, by decide⟩).energy) (xi := (331511611964687 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12796 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12796]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12796])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12796) (a := (10426853273747 / 12500000000000 : ℝ)) (b := (160957885051 / 100000000000000 : ℝ)) (q := (2239915281209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12796])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12796]

theorem cert12797_0 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (84074534015149 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (223971961987 / 10000000000000 : ℝ))
      (E := (cell12797 ⟨0, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (84074534015149 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (223971961987 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_1 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (16807917976263 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239723615389 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨1, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (16807917976263 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239723615389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_2 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (2100116765953 / 2500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111986379679 / 5000000000000 : ℝ))
      (E := (cell12797 ⟨2, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (2100116765953 / 2500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111986379679 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_3 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41984888124579 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (447946324203 / 20000000000000 : ℝ))
      (E := (cell12797 ⟨3, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41984888124579 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (447946324203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_4 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83934906678217 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119867795179 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨4, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83934906678217 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119867795179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_5 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83900061889271 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111986981279 / 5000000000000 : ℝ))
      (E := (cell12797 ⟨5, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83900061889271 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (111986981279 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_6 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83865241846489 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119871809369 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨6, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83865241846489 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119871809369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_7 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41915223257111 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239747577421 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨7, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41915223257111 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239747577421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_8 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83795675857013 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239751624973 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨8, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83795675857013 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239751624973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_9 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41880464919793 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559938898631 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨9, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41880464919793 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559938898631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_10 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83726208426853 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239759608939 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨10, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83726208426853 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239759608939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_11 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83691511583907 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239763616793 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨11, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83691511583907 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239763616793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_12 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (10457104909503 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119883812207 / 50000000000000 : ℝ))
      (E := (cell12797 ⟨12, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (10457104909503 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (1119883812207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_13 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83622191468659 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (17498215921 / 781250000000 : ℝ))
      (E := (cell12797 ⟨13, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83622191468659 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (17498215921 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_14 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (10448446015931 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (279971950613 / 12500000000000 : ℝ))
      (E := (cell12797 ⟨14, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (10448446015931 / 12500000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (279971950613 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_15 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (16710593843641 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559944911831 / 25000000000000 : ℝ))
      (E := (cell12797 ⟨15, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (16710593843641 / 20000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (559944911831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_16 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41759197353461 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239783595983 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨16, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41759197353461 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239783595983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_17 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (41741922279883 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (4479575261 / 200000000000 : ℝ))
      (E := (cell12797 ⟨17, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (41741922279883 / 50000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (4479575261 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_18 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83449318743079 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239791639323 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨18, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83449318743079 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239791639323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12797_19 : CellCertificate 12797 (88400040533741 / 1000000000000000 : ℝ) (328270318919927 / 200000000000000000 : ℝ) (331485084716647 / 10000000000000000 : ℝ)
    (cell12797 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · norm_num [cell12797]
  · have h := gap_lower (n := 12797) (a := (83414817223379 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239795627003 / 100000000000000 : ℝ))
      (E := (cell12797 ⟨19, by decide⟩).energy) (xi := (331485084716647 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12797 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12797]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12797])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12797) (a := (83414817223379 / 100000000000000 : ℝ)) (b := (16094515631 / 10000000000000 : ℝ)) (q := (2239795627003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12797])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12797]

theorem cert12798_0 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (3362980764633 / 4000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119799989063 / 50000000000000 : ℝ))
      (E := (cell12798 ⟨0, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (3362980764633 / 4000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119799989063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_1 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (840395752983 / 1000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239604002713 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨1, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (840395752983 / 1000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239604002713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_2 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (42002328185483 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239608010741 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨2, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (42002328185483 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239608010741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_3 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83969762297419 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559903002723 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨3, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83969762297419 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559903002723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_4 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83934893041447 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (34994000181 / 1562500000000 : ℝ))
      (E := (cell12798 ⟨4, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83934893041447 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (34994000181 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_5 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83900048567027 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239620020983 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨5, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83900048567027 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239620020983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_6 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83865228838327 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119811994519 / 50000000000000 : ℝ))
      (E := (cell12798 ⟨6, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83865228838327 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119811994519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_7 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83830433819701 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559906995329 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨7, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83830433819701 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559906995329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_8 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83795663475691 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (111981600261 / 5000000000000 : ℝ))
      (E := (cell12798 ⟨8, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83795663475691 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (111981600261 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_9 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (5235057360689 / 6250000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559909002467 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨9, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (5235057360689 / 6250000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559909002467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_10 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83726196670611 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (279955000261 / 12500000000000 : ℝ))
      (E := (cell12798 ⟨10, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83726196670611 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (279955000261 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_11 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (41845750069773 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (111982199423 / 5000000000000 : ℝ))
      (E := (cell12798 ⟨11, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (41845750069773 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (111982199423 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_12 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83656828143107 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239648033413 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨12, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83656828143107 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239648033413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_13 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83622180646749 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119826013427 / 50000000000000 : ℝ))
      (E := (cell12798 ⟨13, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83622180646749 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119826013427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_14 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (8358755761611 / 10000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239656032693 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨14, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (8358755761611 / 10000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239656032693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_15 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (20888239754251 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (139978749897 / 6250000000000 : ℝ))
      (E := (cell12798 ⟨15, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (20888239754251 / 25000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (139978749897 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_16 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (1304974762741 / 1562500000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (279958005687 / 12500000000000 : ℝ))
      (E := (cell12798 ⟨16, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (1304974762741 / 1562500000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (279958005687 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_17 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83483834977539 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559917001161 / 25000000000000 : ℝ))
      (E := (cell12798 ⟨17, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83483834977539 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (559917001161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_18 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (83449309469691 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119836027621 / 50000000000000 : ℝ))
      (E := (cell12798 ⟨18, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (83449309469691 / 100000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (1119836027621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12798_19 : CellCertificate 12798 (441986437869049 / 5000000000000000 : ℝ) (1641223302122313 / 1000000000000000000 : ℝ) (331458561764463 / 10000000000000000 : ℝ)
    (cell12798 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · norm_num [cell12798]
  · have h := gap_lower (n := 12798) (a := (41707404129199 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239676027187 / 100000000000000 : ℝ))
      (E := (cell12798 ⟨19, by decide⟩).energy) (xi := (331458561764463 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12798 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12798]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12798])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12798) (a := (41707404129199 / 50000000000000 : ℝ)) (b := (32186485919 / 20000000000000 : ℝ)) (q := (2239676027187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12798])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12798]

theorem cert12799_0 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (84074504218833 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119740223707 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨0, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (84074504218833 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119740223707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_1 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (84039560717577 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239484443313 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨1, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (84039560717577 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239484443313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_2 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (42002321053033 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (17915907387 / 800000000000 : ℝ))
      (E := (cell12799 ⟨2, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (42002321053033 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (17915907387 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_3 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (10496218543487 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (223949245417 / 10000000000000 : ℝ))
      (E := (cell12799 ⟨3, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (10496218543487 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (223949245417 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_4 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (10491859925857 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239496428359 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨4, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (10491859925857 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239496428359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_5 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (20975008811731 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (89580016479 / 4000000000000 : ℝ))
      (E := (cell12799 ⟨5, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (20975008811731 / 25000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (89580016479 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_6 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83865215832269 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (559876103231 / 25000000000000 : ℝ))
      (E := (cell12799 ⟨6, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83865215832269 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (559876103231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_7 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41915210563623 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239508438861 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨7, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41915210563623 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239508438861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_8 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83795651096397 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239512439179 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨8, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83795651096397 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239512439179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_9 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83760905704451 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (559879105239 / 25000000000000 : ℝ))
      (E := (cell12799 ⟨9, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83760905704451 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (559879105239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_10 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (523288655727 / 625000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119760224537 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨10, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (523288655727 / 625000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119760224537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_11 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (836914886971 / 1000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119762207013 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨11, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (836914886971 / 1000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119762207013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_12 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41828408506033 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239528438273 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨12, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41828408506033 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239528438273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_13 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (83622169826679 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (27994155873 / 1250000000000 : ℝ))
      (E := (cell12799 ⟨13, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (83622169826679 / 100000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (27994155873 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_14 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41793773553287 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119768228209 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨14, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41793773553287 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119768228209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_15 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (2611029650549 / 3125000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239540461697 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨15, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (2611029650549 / 3125000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239540461697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_16 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41759187462827 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119772216413 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨16, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41759187462827 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119772216413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_17 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (41741912698501 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239548433057 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨17, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (41741912698501 / 50000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239548433057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_18 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (16689860039591 / 20000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239552467251 / 100000000000000 : ℝ))
      (E := (cell12799 ⟨18, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (16689860039591 / 20000000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (2239552467251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

theorem cert12799_19 : CellCertificate 12799 (3452911524477 / 39062500000000 : ℝ) (328219005939759 / 200000000000000000 : ℝ) (82858010776753 / 2500000000000000 : ℝ)
    (cell12799 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · norm_num [cell12799]
  · have h := gap_lower (n := 12799) (a := (10426849911879 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119778240881 / 50000000000000 : ℝ))
      (E := (cell12799 ⟨19, by decide⟩).energy) (xi := (82858010776753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12799 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12799]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12799])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12799) (a := (10426849911879 / 12500000000000 : ℝ)) (b := (32183940981 / 20000000000000 : ℝ)) (q := (1119778240881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12799])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12799]

end BstLean.Part268
