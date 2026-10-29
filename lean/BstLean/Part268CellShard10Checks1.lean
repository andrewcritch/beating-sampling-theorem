import BstLean.Part268CellShard10Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12600_20 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (16676415340051 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (283000512487 / 12500000000000 : ℝ))
      (E := (cell12600 ⟨20, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (16676415340051 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (283000512487 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_21 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (20836890588871 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (8843781753 / 390625000000 : ℝ))
      (E := (cell12600 ⟨21, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (20836890588871 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (8843781753 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_22 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83313072293793 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (226401212257 / 10000000000000 : ℝ))
      (E := (cell12600 ⟨22, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83313072293793 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (226401212257 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_23 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (8327860648221 / 10000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264016085207 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨23, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (8327860648221 / 10000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264016085207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_24 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (650345038187 / 781250000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (283002517133 / 12500000000000 : ℝ))
      (E := (cell12600 ⟨24, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (650345038187 / 781250000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (283002517133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_25 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83209747478339 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (566006026639 / 25000000000000 : ℝ))
      (E := (cell12600 ⟨25, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83209747478339 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (566006026639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_26 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41587677110477 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (283003514203 / 12500000000000 : ℝ))
      (E := (cell12600 ⟨26, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41587677110477 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (283003514203 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_27 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83140985083483 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264032102867 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨27, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83140985083483 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264032102867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_28 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83106640033793 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132018067733 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨28, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83106640033793 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132018067733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_29 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83072319039917 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264040097029 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨29, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83072319039917 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264040097029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_30 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83038022070051 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264044106753 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨30, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83038022070051 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264044106753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_31 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (83003749092551 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264048108217 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨31, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (83003749092551 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264048108217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_32 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (41484750037969 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (90562084129 / 4000000000000 : ℝ))
      (E := (cell12600 ⟨32, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (41484750037969 / 50000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (90562084129 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_33 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (20733818747223 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264056093353 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨33, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (20733818747223 / 25000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264056093353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_34 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82901073800251 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264060138547 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨34, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82901073800251 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264060138547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_35 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82866896479013 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132032061379 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨35, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82866896479013 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132032061379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_36 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (16566548598867 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264068105457 / 100000000000000 : ℝ))
      (E := (cell12600 ⟨36, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (16566548598867 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (2264068105457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_37 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82798613315529 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132036072991 / 50000000000000 : ℝ))
      (E := (cell12600 ⟨37, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82798613315529 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (1132036072991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_38 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (82764507412061 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (141504757967 / 6250000000000 : ℝ))
      (E := (cell12600 ⟨38, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (82764507412061 / 100000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (141504757967 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12600_39 : CellCertificate 12600 (444752755420233 / 5000000000000000 : ℝ) (833511250534181 / 500000000000000000 : ℝ) (168397677141071 / 5000000000000000 : ℝ)
    (cell12600 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · norm_num [cell12600]
  · have h := gap_lower (n := 12600) (a := (16546085050711 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (452816021759 / 20000000000000 : ℝ))
      (E := (cell12600 ⟨39, by decide⟩).energy) (xi := (168397677141071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12600 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12600]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12600])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12600) (a := (16546085050711 / 20000000000000 : ℝ)) (b := (1021827981 / 625000000000 : ℝ)) (q := (452816021759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12600])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12600]

theorem cert12601_20 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41691033862211 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263877684763 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨20, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41691033862211 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263877684763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_21 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41673776847323 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (452776337727 / 20000000000000 : ℝ))
      (E := (cell12601 ⟨21, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41673776847323 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (452776337727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_22 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83313063947509 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131942829077 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨22, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83313063947509 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131942829077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_23 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83278598450043 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131944827779 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨23, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83278598450043 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131944827779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_24 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (10405519646181 / 12500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263893684581 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨24, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (10405519646181 / 12500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263893684581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_25 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (20802435018273 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131948845169 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨25, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (20802435018273 / 25000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131948845169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_26 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (1299614798883 / 1562500000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (113195083801 / 5000000000000 : ℝ))
      (E := (cell12601 ⟨26, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (1299614798883 / 1562500000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (113195083801 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_27 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (8314097830341 / 10000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263905644587 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨27, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (8314097830341 / 10000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263905644587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_28 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (10388329195707 / 12500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263909657221 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨28, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (10388329195707 / 12500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263909657221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_29 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83072312883283 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131956829003 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨29, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83072312883283 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131956829003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_30 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (16607603244897 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131958824603 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨30, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (16607603244897 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131958824603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_31 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (83003743557623 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263921691379 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨31, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (83003743557623 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263921691379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_32 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (5185593428201 / 6250000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263925669301 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨32, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (5185593428201 / 6250000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263925669301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_33 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (16587054014789 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131964850811 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨33, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (16587054014789 / 20000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131964850811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_34 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82901069194651 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131966836283 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨34, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82901069194651 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131966836283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_35 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82866892182331 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131968850213 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨35, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82866892182331 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131968850213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_36 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82832739006143 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263941668881 / 100000000000000 : ℝ))
      (E := (cell12601 ⟨36, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82832739006143 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (2263941668881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_37 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (413993048177 / 500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (282993211983 / 12500000000000 : ℝ))
      (E := (cell12601 ⟨37, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (413993048177 / 500000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (282993211983 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_38 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (82764504039569 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (452789932903 / 20000000000000 : ℝ))
      (E := (cell12601 ⟨38, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (82764504039569 / 100000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (452789932903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12601_39 : CellCertificate 12601 (222369287192781 / 2500000000000000 : ℝ) (1666890164356337 / 1000000000000000000 : ℝ) (33676796267151 / 1000000000000000 : ℝ)
    (cell12601 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · norm_num [cell12601]
  · have h := gap_lower (n := 12601) (a := (41365211094137 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131976846207 / 50000000000000 : ℝ))
      (E := (cell12601 ⟨39, by decide⟩).energy) (xi := (33676796267151 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12601 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12601]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12601])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12601) (a := (41365211094137 / 50000000000000 : ℝ)) (b := (81739670623 / 50000000000000 : ℝ)) (q := (1131976846207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12601])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12601]

theorem cert12602_20 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10422757343781 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131875632793 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨20, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10422757343781 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131875632793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_21 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (20836886258857 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131877622249 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨21, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (20836886258857 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131877622249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_22 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10414131950351 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131879624043 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨22, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10414131950351 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131879624043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_23 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (83278590419419 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131881640161 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨23, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (83278590419419 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131881640161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_24 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (5202759340779 / 6250000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565941807053 / 25000000000000 : ℝ))
      (E := (cell12602 ⟨24, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (5202759340779 / 6250000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (565941807053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_25 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (83209732669311 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263771270273 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨25, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (83209732669311 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263771270273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_26 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41587670018749 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (141485952163 / 6250000000000 : ℝ))
      (E := (cell12602 ⟨26, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41587670018749 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (141485952163 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_27 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10392621440591 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263779240971 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨27, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10392621440591 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263779240971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_28 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (10388328387359 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131891616851 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨28, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (10388328387359 / 12500000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131891616851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_29 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41536153363981 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263787273773 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨29, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41536153363981 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263787273773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_30 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (16607602076039 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263791246511 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨30, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (16607602076039 / 20000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263791246511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_31 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (20750934505983 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (226379527093 / 10000000000000 : ℝ))
      (E := (cell12602 ⟨31, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (20750934505983 / 25000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (226379527093 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_32 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41484744813847 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263799290353 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨32, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41484744813847 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263799290353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_33 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82935265160161 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263803247781 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨33, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82935265160161 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263803247781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_34 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (3316042583607 / 4000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131903630843 / 50000000000000 : ℝ))
      (E := (cell12602 ⟨34, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (3316042583607 / 4000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (1131903630843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_35 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (5179180492921 / 6250000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263811274637 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨35, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (5179180492921 / 6250000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263811274637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_36 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82832735019 / 100000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (226381528753 / 10000000000000 : ℝ))
      (E := (cell12602 ⟨36, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82832735019 / 100000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (226381528753 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_37 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (41399302978141 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263819242367 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨37, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (41399302978141 / 50000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263819242367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_38 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (1655290013361 / 2000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263823256907 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨38, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (1655290013361 / 2000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263823256907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12602_39 : CellCertificate 12602 (44472439551351 / 500000000000000 : ℝ) (416689462163441 / 250000000000000000 : ℝ) (168370287793637 / 5000000000000000 : ℝ)
    (cell12602 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · norm_num [cell12602]
  · have h := gap_lower (n := 12602) (a := (82730419123929 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263827272731 / 100000000000000 : ℝ))
      (E := (cell12602 ⟨39, by decide⟩).energy) (xi := (168370287793637 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12602 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12602]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12602])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12602) (a := (82730419123929 / 100000000000000 : ℝ)) (b := (8173310383 / 5000000000000 : ℝ)) (q := (2263827272731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12602])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12602]

theorem cert12603_20 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83382049777733 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452724980127 / 20000000000000 : ℝ))
      (E := (cell12603 ⟨20, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83382049777733 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452724980127 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_21 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (8334753637783 / 10000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131814456471 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨21, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (8334753637783 / 10000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131814456471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_22 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (10414130907461 / 12500000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565908223093 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨22, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (10414130907461 / 12500000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565908223093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_23 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83278582390339 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131818450581 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨23, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83278582390339 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131818450581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_24 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (16648828347397 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565910221171 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨24, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (16648828347397 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565910221171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_25 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83209725266997 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565911226187 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨25, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83209725266997 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565911226187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_26 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (10396916618489 / 12500000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (70739028319 / 3125000000000 : ℝ))
      (E := (cell12603 ⟨26, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (10396916618489 / 12500000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (70739028319 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_27 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (20785241186859 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263652892021 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨27, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (20785241186859 / 25000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263652892021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_28 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83106620633439 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263656864911 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨28, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83106620633439 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263656864911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_29 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (41536150286977 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565915221463 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨29, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (41536150286977 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565915221463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_30 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83038004537181 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263664898669 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨30, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83038004537181 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263664898669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_31 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (83003732491479 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565917226349 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨31, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (83003732491479 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565917226349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_32 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82969484405371 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263672907833 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨32, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82969484405371 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263672907833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_33 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82935260247539 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452735381511 / 20000000000000 : ℝ))
      (E := (cell12603 ⟨33, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82935260247539 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (452735381511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_34 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (10362632498353 / 12500000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565920226477 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨34, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (10362632498353 / 12500000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565920226477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_35 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82866883592227 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565921226003 / 25000000000000 : ℝ))
      (E := (cell12603 ⟨35, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82866883592227 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (565921226003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_36 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (41416365516453 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263688902761 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨36, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (41416365516453 / 50000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263688902761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_37 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (3311944091127 / 4000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131846451413 / 50000000000000 : ℝ))
      (E := (cell12603 ⟨37, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (3311944091127 / 4000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (1131846451413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_38 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (16552899459501 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263696904651 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨38, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (16552899459501 / 20000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263696904651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12603_39 : CellCertificate 12603 (177884087521423 / 2000000000000000 : ℝ) (833312776977819 / 500000000000000000 : ℝ) (84178298257051 / 2500000000000000 : ℝ)
    (cell12603 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · norm_num [cell12603]
  · have h := gap_lower (n := 12603) (a := (82730416060521 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263700908459 / 100000000000000 : ℝ))
      (E := (cell12603 ⟨39, by decide⟩).energy) (xi := (84178298257051 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12603 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12603]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12603])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12603) (a := (82730416060521 / 100000000000000 : ℝ)) (b := (163453076201 / 100000000000000 : ℝ)) (q := (2263700908459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12603])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12603]

theorem cert12604_20 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (20845510201719 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131749265821 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨20, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (20845510201719 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131749265821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_21 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (20836881930463 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (282937822173 / 12500000000000 : ℝ))
      (E := (cell12604 ⟨21, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (20836881930463 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (282937822173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_22 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83313038918149 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131753266347 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨22, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83313038918149 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131753266347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_23 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83278574362801 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131755288209 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨23, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83278574362801 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131755288209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_24 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (8324413402301 / 10000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263514537271 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨24, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (8324413402301 / 10000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263514537271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_25 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (20802429466537 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263518535379 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨25, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (20802429466537 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263518535379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_26 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41587662929877 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263522574003 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨26, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41587662929877 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263522574003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_27 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41570478985767 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (282940817413 / 12500000000000 : ℝ))
      (E := (cell12604 ⟨27, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41570478985767 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (282940817413 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_28 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83106614169357 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (45270611017 / 2000000000000 : ℝ))
      (E := (cell12604 ⟨28, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83106614169357 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (45270611017 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_29 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (83072294421261 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263534552721 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨29, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (83072294421261 / 100000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263534552721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_30 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41518999347721 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131769273589 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨30, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41518999347721 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131769273589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_31 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (10375465870033 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131771297389 / 50000000000000 : ℝ))
      (E := (cell12604 ⟨31, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (10375465870033 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (1131771297389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_32 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (10371184898031 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (565886645073 / 25000000000000 : ℝ))
      (E := (cell12604 ⟨32, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (10371184898031 / 12500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (565886645073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_33 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41467627668039 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263550563797 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨33, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41467627668039 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263550563797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_34 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (20725263846149 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263554546637 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨34, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (20725263846149 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263554546637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_35 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (20716719824701 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263558588553 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨35, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (20716719824701 / 25000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263558588553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_36 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (4141636352393 / 5000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263562573221 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨36, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (4141636352393 / 5000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263562573221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_37 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (2069964965027 / 2500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (452713311981 / 20000000000000 : ℝ))
      (E := (cell12604 ⟨37, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (2069964965027 / 2500000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (452713311981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_38 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (41382246963967 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263570549053 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨38, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (41382246963967 / 50000000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263570549053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12604_39 : CellCertificate 12604 (444696044255187 / 5000000000000000 : ℝ) (1666493280256959 / 1000000000000000000 : ℝ) (336685814993073 / 10000000000000000 : ℝ)
    (cell12604 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · norm_num [cell12604]
  · have h := gap_lower (n := 12604) (a := (2585325406189 / 3125000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263574599601 / 100000000000000 : ℝ))
      (E := (cell12604 ⟨39, by decide⟩).energy) (xi := (336685814993073 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12604 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12604]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12604])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12604) (a := (2585325406189 / 3125000000000 : ℝ)) (b := (163439946869 / 100000000000000 : ℝ)) (q := (2263574599601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12604])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12604]

theorem cert12605_20 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20845507959419 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131686137573 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨20, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20845507959419 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131686137573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_21 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83347519067493 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565844074029 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨21, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83347519067493 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565844074029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_22 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83313030578191 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131690142843 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨22, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83313030578191 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131690142843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_23 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (16655713267361 / 20000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (282923030969 / 12500000000000 : ℝ))
      (E := (cell12605 ⟨23, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (16655713267361 / 20000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (282923030969 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_24 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (4162206315527 / 5000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (141461765271 / 6250000000000 : ℝ))
      (E := (cell12605 ⟨24, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (4162206315527 / 5000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (141461765271 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_25 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41604855233383 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263392278937 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨25, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41604855233383 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263392278937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_26 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (2599228711657 / 3125000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131698148201 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨26, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (2599228711657 / 3125000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131698148201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_27 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (4157047559851 / 5000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263400299689 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨27, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (4157047559851 / 5000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263400299689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_28 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83106607706627 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131702145759 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨28, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83106607706627 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131702145759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_29 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (2076807206747 / 2500000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131704137191 / 50000000000000 : ℝ))
      (E := (cell12605 ⟨29, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (2076807206747 / 2500000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (1131704137191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_30 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (83037992854979 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263412250541 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨30, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (83037992854979 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263412250541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_31 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41501860715143 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (45268325611 / 2000000000000 : ℝ))
      (E := (cell12605 ⟨31, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41501860715143 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (45268325611 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_32 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20742368491081 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263420307731 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨32, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20742368491081 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263420307731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_33 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82935250425779 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263424275079 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨33, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82935250425779 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263424275079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_34 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (20725262695873 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263428301067 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨34, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (20725262695873 / 25000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263428301067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_35 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (82866875006467 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263432269639 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨35, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (82866875006467 / 100000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263432269639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_36 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41416361531931 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565859074727 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨36, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41416361531931 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565859074727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_37 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (41399297462497 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565860068069 / 25000000000000 : ℝ))
      (E := (cell12605 ⟨37, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (41399297462497 / 50000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (565860068069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_38 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (16552898111867 / 20000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (905377723 / 40000000000 : ℝ))
      (E := (cell12605 ⟨38, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (16552898111867 / 20000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (905377723 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12605_39 : CellCertificate 12605 (889363743735761 / 10000000000000000 : ℝ) (1666361027552727 / 1000000000000000000 : ℝ) (336658441480651 / 10000000000000000 : ℝ)
    (cell12605 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · norm_num [cell12605]
  · have h := gap_lower (n := 12605) (a := (8273040993651 / 10000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263448287443 / 100000000000000 : ℝ))
      (E := (cell12605 ⟨39, by decide⟩).energy) (xi := (336658441480651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12605 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12605]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12605])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12605) (a := (8273040993651 / 10000000000000 : ℝ)) (b := (10214176229 / 6250000000000 : ℝ)) (q := (2263448287443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12605])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12605]

theorem cert12606_20 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (41691011435067 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (226324601461 / 10000000000000 : ℝ))
      (E := (cell12606 ⟨20, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (41691011435067 / 50000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (226324601461 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_21 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (2604609700461 / 3125000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (45265000217 / 2000000000000 : ℝ))
      (E := (cell12606 ⟨21, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (2604609700461 / 3125000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (45265000217 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_22 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83313022239813 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131627017359 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨22, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83313022239813 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131627017359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_23 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (2602454947261 / 3125000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131629015921 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨23, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (2602454947261 / 3125000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131629015921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_24 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (20811029649893 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452652401177 / 20000000000000 : ℝ))
      (E := (cell12606 ⟨24, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (20811029649893 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452652401177 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_25 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83209703068849 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263266018653 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨25, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83209703068849 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263266018653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_26 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83175311687721 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131635007499 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨26, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83175311687721 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131635007499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_27 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (10392618052987 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263274056309 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨27, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (10392618052987 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263274056309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_28 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (83106601245247 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131639014231 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨28, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (83106601245247 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131639014231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_29 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (20768070529953 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263282050839 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨29, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (20768070529953 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263282050839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_30 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (8303798701579 / 10000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263286008761 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨30, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (8303798701579 / 10000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263286008761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_31 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (10375464487693 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131645010621 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨31, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (10375464487693 / 12500000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131645010621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_32 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (82969468745599 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (5658235079 / 250000000000 : ℝ))
      (E := (cell12606 ⟨32, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (82969468745599 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (5658235079 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_33 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (518345284479 / 625000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131649020703 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨33, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (518345284479 / 625000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131649020703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_34 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (82901046183511 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131651026003 / 50000000000000 : ℝ))
      (E := (cell12606 ⟨34, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (82901046183511 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (1131651026003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_35 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (16573374143043 / 20000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452661212903 / 20000000000000 : ℝ))
      (E := (cell12606 ⟨35, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (16573374143043 / 20000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (452661212903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_36 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (5177044942557 / 6250000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263310021181 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨36, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (5177044942557 / 6250000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263310021181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_37 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (82798591249919 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263314039939 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨37, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (82798591249919 / 100000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263314039939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_38 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (20691121797927 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263318062611 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨38, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (20691121797927 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263318062611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12606_39 : CellCertificate 12606 (2779173135257 / 31250000000000 : ℝ) (333245759167589 / 200000000000000000 : ℝ) (21039442030607 / 625000000000000 : ℝ)
    (cell12606 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · norm_num [cell12606]
  · have h := gap_lower (n := 12606) (a := (20682601718977 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263322030701 / 100000000000000 : ℝ))
      (E := (cell12606 ⟨39, by decide⟩).energy) (xi := (21039442030607 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12606 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12606]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12606])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12606) (a := (20682601718977 / 25000000000000 : ℝ)) (b := (20426711823 / 12500000000000 : ℝ)) (q := (2263322030701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12606])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12606]

theorem cert12607_20 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83382013904249 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452623961661 / 20000000000000 : ℝ))
      (E := (cell12607 ⟨20, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83382013904249 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452623961661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_21 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (8334750176363 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (282890479771 / 12500000000000 : ℝ))
      (E := (cell12607 ⟨21, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (8334750176363 / 10000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (282890479771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_22 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (16662602780603 / 20000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452625567621 / 20000000000000 : ℝ))
      (E := (cell12607 ⟨22, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (16662602780603 / 20000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452625567621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_23 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (520490939309 / 625000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263131812013 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨23, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (520490939309 / 625000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263131812013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_24 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (20811027722527 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131567910957 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨24, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (20811027722527 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131567910957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_25 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (20802423918099 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131569906457 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨25, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (20802423918099 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131569906457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_26 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (20793826150961 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263143846611 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨26, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (20793826150961 / 25000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263143846611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_27 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (259815430163 / 312500000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452629561833 / 20000000000000 : ℝ))
      (E := (cell12607 ⟨27, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (259815430163 / 312500000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452629561833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_28 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (41553297392609 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131575910069 / 50000000000000 : ℝ))
      (E := (cell12607 ⟨28, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (41553297392609 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (1131575910069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_29 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (5192017248191 / 6250000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (226315582361 / 10000000000000 : ℝ))
      (E := (cell12607 ⟨29, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (5192017248191 / 6250000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (226315582361 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_30 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (664303849423 / 800000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263159821839 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨30, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (664303849423 / 800000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263159821839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_31 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (83003710374039 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (565790954213 / 25000000000000 : ℝ))
      (E := (cell12607 ⟨31, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (83003710374039 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (565790954213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_32 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82969463528073 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (45263356209 / 2000000000000 : ℝ))
      (E := (cell12607 ⟨32, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82969463528073 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (45263356209 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_33 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (41467620304331 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263171804203 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨33, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (41467620304331 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263171804203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_34 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82901041584653 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (45263517161 / 2000000000000 : ℝ))
      (E := (cell12607 ⟨34, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82901041584653 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (45263517161 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_35 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (10358358303131 / 12500000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263179855937 / 100000000000000 : ℝ))
      (E := (cell12607 ⟨35, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (10358358303131 / 12500000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (2263179855937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_36 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82832715099009 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (226318385733 / 10000000000000 : ℝ))
      (E := (cell12607 ⟨36, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82832715099009 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (226318385733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_37 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (82798587575853 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452637572579 / 20000000000000 : ℝ))
      (E := (cell12607 ⟨37, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (82798587575853 / 100000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (452637572579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_38 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (41382241912527 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (141449488399 / 6250000000000 : ℝ))
      (E := (cell12607 ⟨38, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (41382241912527 / 50000000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (141449488399 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12607_39 : CellCertificate 12607 (35572282685951 / 400000000000000 : ℝ) (52065518284613 / 31250000000000000 : ℝ) (84150927004757 / 2500000000000000 : ℝ)
    (cell12607 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · norm_num [cell12607]
  · have h := gap_lower (n := 12607) (a := (1034130047703 / 1250000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (3621113327 / 160000000000 : ℝ))
      (E := (cell12607 ⟨39, by decide⟩).energy) (xi := (84150927004757 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12607 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12607]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12607])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12607) (a := (1034130047703 / 1250000000000 : ℝ)) (b := (16340057163 / 10000000000000 : ℝ)) (q := (3621113327 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12607])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12607]

theorem cert12608_20 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (4169100247001 / 5000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262993656231 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨20, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (4169100247001 / 5000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2262993656231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_21 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41673746557063 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (141437353843 / 6250000000000 : ℝ))
      (E := (cell12608 ⟨21, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41673746557063 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (141437353843 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_22 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83313005567797 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131500818767 / 50000000000000 : ℝ))
      (E := (cell12608 ⟨22, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83313005567797 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131500818767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_23 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83278542268069 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263005646603 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨23, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83278542268069 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263005646603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_24 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83244103182147 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263009634063 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨24, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83244103182147 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263009634063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_25 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (2600302758669 / 3125000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (56575341543 / 2500000000000 : ℝ))
      (E := (cell12608 ⟨25, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (2600302758669 / 3125000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (56575341543 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_26 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83175297521393 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263017674423 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨26, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83175297521393 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263017674423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_27 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (20785232720453 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (18104173401 / 800000000000 : ℝ))
      (E := (cell12608 ⟨27, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (20785232720453 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (18104173401 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_28 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83106588326539 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263025666547 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨28, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83106588326539 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263025666547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_29 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (20768067455903 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282878706397 / 12500000000000 : ℝ))
      (E := (cell12608 ⟨29, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (20768067455903 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (282878706397 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_30 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41518987670617 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263033631271 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨30, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41518987670617 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263033631271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_31 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (83003704847769 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452607533477 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨31, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (83003704847769 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452607533477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_32 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (1296397786121 / 1562500000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452608328857 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨32, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (1296397786121 / 1562500000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452608328857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_33 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (16587047140369 / 20000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131522840309 / 50000000000000 : ℝ))
      (E := (cell12608 ⟨33, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (16587047140369 / 20000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (1131522840309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_34 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41450518493459 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565762415151 / 25000000000000 : ℝ))
      (E := (cell12608 ⟨34, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41450518493459 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565762415151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_35 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41433431067983 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565763410977 / 25000000000000 : ℝ))
      (E := (cell12608 ⟨35, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41433431067983 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (565763410977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_36 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41416355559077 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452611538013 / 20000000000000 : ℝ))
      (E := (cell12608 ⟨36, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41416355559077 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (452611538013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_37 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (41399291951399 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (90522467299 / 4000000000000 : ℝ))
      (E := (cell12608 ⟨37, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (41399291951399 / 50000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (90522467299 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_38 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (20691120114843 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263065680203 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨38, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (20691120114843 / 25000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263065680203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12608_39 : CellCertificate 12608 (222319683833583 / 2500000000000000 : ℝ) (333192879071349 / 200000000000000000 : ℝ) (84144087016843 / 2500000000000000 : ℝ)
    (cell12608 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · norm_num [cell12608]
  · have h := gap_lower (n := 12608) (a := (82730400757507 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263069683467 / 100000000000000 : ℝ))
      (E := (cell12608 ⟨39, by decide⟩).energy) (xi := (84144087016843 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12608 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12608]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12608])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12608) (a := (82730400757507 / 100000000000000 : ℝ)) (b := (163387450801 / 100000000000000 : ℝ)) (q := (2263069683467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12608])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12608]

theorem cert12609_20 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83381995977447 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131433750061 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨20, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83381995977447 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131433750061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_21 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (260460888957 / 312500000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452574307821 / 20000000000000 : ℝ))
      (E := (cell12609 ⟨21, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (260460888957 / 312500000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452574307821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_22 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41656498617079 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262875549639 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨22, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41656498617079 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262875549639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_23 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41639267124119 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262879535617 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨23, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41639267124119 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262879535617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_24 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (10405511934461 / 12500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131441750349 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨24, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (10405511934461 / 12500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131441750349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_25 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (20802420220971 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (8839404323 / 390625000000 : ℝ))
      (E := (cell12609 ⟨25, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (20802420220971 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (8839404323 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_26 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83175290440369 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452578299687 / 20000000000000 : ℝ))
      (E := (cell12609 ⟨26, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83175290440369 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452578299687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_27 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (20785231028213 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131447768663 / 50000000000000 : ℝ))
      (E := (cell12609 ⟨27, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (20785231028213 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (1131447768663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_28 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83106581869209 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452579901847 / 20000000000000 : ℝ))
      (E := (cell12609 ⟨28, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83106581869209 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (452579901847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_29 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (2076806591937 / 2500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262903533541 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨29, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (2076806591937 / 2500000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262903533541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_30 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (83037969505867 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262907554067 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨30, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (83037969505867 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262907554067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_31 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (5187731207671 / 6250000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (282863939289 / 12500000000000 : ℝ))
      (E := (cell12609 ⟨31, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (5187731207671 / 6250000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (282863939289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_32 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82969453096613 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (141432220819 / 6250000000000 : ℝ))
      (E := (cell12609 ⟨32, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82969453096613 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (141432220819 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_33 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82935230796187 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565729888377 / 25000000000000 : ℝ))
      (E := (cell12609 ⟨33, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82935230796187 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565729888377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_34 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (2590657262197 / 3125000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565730879567 / 25000000000000 : ℝ))
      (E := (cell12609 ⟨34, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (2590657262197 / 3125000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (565730879567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_35 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82866857847969 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (282865943209 / 12500000000000 : ℝ))
      (E := (cell12609 ⟨35, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82866857847969 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (282865943209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_36 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (16566541427669 / 20000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262931519389 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨36, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (16566541427669 / 20000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262931519389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_37 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (82798580230751 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262935557353 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨37, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (82798580230751 / 100000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262935557353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_38 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (41382238547331 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262939542689 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨38, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (41382238547331 / 50000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262939542689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12609_39 : CellCertificate 12609 (444625203918937 / 5000000000000000 : ℝ) (1665832226580339 / 1000000000000000000 : ℝ) (336548992633519 / 10000000000000000 : ℝ)
    (cell12609 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · norm_num [cell12609]
  · have h := gap_lower (n := 12609) (a := (20682599424927 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262943534263 / 100000000000000 : ℝ))
      (E := (cell12609 ⟨39, by decide⟩).energy) (xi := (336548992633519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12609 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12609]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12609])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12609) (a := (20682599424927 / 25000000000000 : ℝ)) (b := (32674866419 / 20000000000000 : ℝ)) (q := (2262943534263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12609])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12609]

theorem cert12610_20 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (8338198701653 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565685364129 / 25000000000000 : ℝ))
      (E := (cell12610 ⟨20, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (8338198701653 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565685364129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_21 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (8334747581997 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131372706363 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨21, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (8334747581997 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131372706363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_22 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83312988902097 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131374728893 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨22, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83312988902097 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131374728893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_23 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (20819631557487 / 25000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (282844177589 / 12500000000000 : ℝ))
      (E := (cell12610 ⟨23, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (20819631557487 / 25000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (282844177589 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_24 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (20811021942683 / 25000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (282844677727 / 12500000000000 : ℝ))
      (E := (cell12610 ⟨24, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (20811021942683 / 25000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (282844677727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_25 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (5200604593239 / 6250000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (226276146459 / 10000000000000 : ℝ))
      (E := (cell12610 ⟨25, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (5200604593239 / 6250000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (226276146459 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_26 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (8317528336077 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262765435467 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨26, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (8317528336077 / 10000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262765435467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_27 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83140917345279 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262769454199 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨27, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83140917345279 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262769454199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_28 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83106575413229 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452554693023 / 20000000000000 : ℝ))
      (E := (cell12610 ⟨28, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83106575413229 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452554693023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_29 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (41536128766329 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (141423591919 / 6250000000000 : ℝ))
      (E := (cell12610 ⟨29, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (41536128766329 / 50000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (141423591919 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_30 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83037963671773 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262781473219 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨30, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83037963671773 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262781473219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_31 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (83003693798937 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262785474689 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨31, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (83003693798937 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262785474689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_32 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (2074236197067 / 2500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565697369227 / 25000000000000 : ℝ))
      (E := (cell12610 ⟨32, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (2074236197067 / 2500000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (565697369227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_33 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82935225891689 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (226279342287 / 10000000000000 : ℝ))
      (E := (cell12610 ⟨33, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82935225891689 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (226279342287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_34 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82901027794813 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262797431041 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨34, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82901027794813 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262797431041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_35 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (2589589173783 / 3125000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452560288797 / 20000000000000 : ℝ))
      (E := (cell12610 ⟨35, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (2589589173783 / 3125000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (452560288797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_36 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82832703159583 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (35356335353 / 1562500000000 : ℝ))
      (E := (cell12610 ⟨36, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82832703159583 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (35356335353 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_37 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82798576559713 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (282851178607 / 12500000000000 : ℝ))
      (E := (cell12610 ⟨37, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82798576559713 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (282851178607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_38 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82764473730923 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262813460533 / 100000000000000 : ℝ))
      (E := (cell12610 ⟨38, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82764473730923 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (2262813460533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12610_39 : CellCertificate 12610 (889222084658369 / 10000000000000000 : ℝ) (832850039386703 / 500000000000000000 : ℝ) (336521641716243 / 10000000000000000 : ℝ)
    (cell12610 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · norm_num [cell12610]
  · have h := gap_lower (n := 12610) (a := (82730394642843 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131408720239 / 50000000000000 : ℝ))
      (E := (cell12610 ⟨39, by decide⟩).energy) (xi := (336521641716243 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12610 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12610]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12610])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12610) (a := (82730394642843 / 100000000000000 : ℝ)) (b := (81680607757 / 50000000000000 : ℝ)) (q := (1131408720239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12610])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12610]

theorem cert12611_20 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (20845494514317 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (18100923271 / 800000000000 : ℝ))
      (E := (cell12611 ⟨20, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (20845494514317 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (18100923271 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_21 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41673733587659 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262619398937 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨21, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41673733587659 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262619398937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_22 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (16662596114323 / 20000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (452524684059 / 20000000000000 : ℝ))
      (E := (cell12611 ⟨22, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (16662596114323 / 20000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (452524684059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_23 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41639259106599 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262627418571 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨23, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41639259106599 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262627418571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_24 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (20811020016819 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131315698711 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨24, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (20811020016819 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131315698711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_25 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83209666101227 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131317709327 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨25, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83209666101227 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131317709327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_26 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (20793819070649 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262639368701 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨26, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (20793819070649 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262639368701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_27 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41570455289547 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (141415210457 / 6250000000000 : ℝ))
      (E := (cell12611 ⟨27, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41570455289547 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (141415210457 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_28 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83106568958597 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (90505896691 / 4000000000000 : ℝ))
      (E := (cell12611 ⟨28, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83106568958597 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (90505896691 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_29 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (20768062847287 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (452530280837 / 20000000000000 : ℝ))
      (E := (cell12611 ⟨29, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (20768062847287 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (452530280837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_30 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (83037957838951 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (226265538873 / 10000000000000 : ℝ))
      (E := (cell12611 ⟨30, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (83037957838951 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (226265538873 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_31 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (41501844138187 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (452531874587 / 20000000000000 : ℝ))
      (E := (cell12611 ⟨31, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (41501844138187 / 50000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (452531874587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_32 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (10371180333743 / 12500000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262663417147 / 100000000000000 : ℝ))
      (E := (cell12611 ⟨32, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (10371180333743 / 12500000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (2262663417147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_33 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82935220988351 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131333702927 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨33, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82935220988351 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131333702927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_34 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82901023200443 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (90506855957 / 4000000000000 : ℝ))
      (E := (cell12611 ⟨34, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82901023200443 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (90506855957 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_35 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82866849275227 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (70708606171 / 3125000000000 : ℝ))
      (E := (cell12611 ⟨35, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82866849275227 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (70708606171 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_36 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (82832699181867 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (141417462649 / 6250000000000 : ℝ))
      (E := (cell12611 ⟨36, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (82832699181867 / 100000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (141417462649 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_37 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (20699643222421 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131341707163 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨37, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (20699643222421 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131341707163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_38 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (20691117592039 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131343716867 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨38, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (20691117592039 / 25000000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131343716867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12611_39 : CellCertificate 12611 (444596882897391 / 5000000000000000 : ℝ) (1665567951930957 / 1000000000000000000 : ℝ) (4206178691429 / 125000000000000 : ℝ)
    (cell12611 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · norm_num [cell12611]
  · have h := gap_lower (n := 12611) (a := (2585324737091 / 3125000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131345701057 / 50000000000000 : ℝ))
      (E := (cell12611 ⟨39, by decide⟩).energy) (xi := (4206178691429 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12611 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12611]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12611])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12611) (a := (2585324737091 / 3125000000000 : ℝ)) (b := (2552314079 / 1562500000000 : ℝ)) (q := (1131345701057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12611])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12611]

theorem cert12612_20 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (4169098454983 / 5000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262489357203 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨20, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (4169098454983 / 5000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262489357203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_21 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41673729266141 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (565623345289 / 25000000000000 : ℝ))
      (E := (cell12612 ⟨21, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41673729266141 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (565623345289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_22 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83312972242711 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (45249947577 / 2000000000000 : ℝ))
      (E := (cell12612 ⟨22, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83312972242711 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (45249947577 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_23 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (20819627549497 / 25000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (565625353129 / 25000000000000 : ℝ))
      (E := (cell12612 ⟨23, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (20819627549497 / 25000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (565625353129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_24 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41622036182661 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262505369153 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨24, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41622036182661 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262505369153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_25 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41604829356047 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131254684441 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨25, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41604829356047 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131254684441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_26 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83175269205847 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262513414959 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨26, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83175269205847 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262513414959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_27 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41570451907147 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262517393537 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨27, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41570451907147 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262517393537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_28 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41553281252657 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262521365717 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨28, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41553281252657 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262521365717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_29 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83072245246949 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262525392467 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨29, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83072245246949 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262525392467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_30 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (83037952007403 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (282816177201 / 12500000000000 : ℝ))
      (E := (cell12612 ⟨30, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (83037952007403 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (282816177201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_31 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (16600736551009 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452506676927 / 20000000000000 : ℝ))
      (E := (cell12612 ⟨31, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (16600736551009 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452506676927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_32 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (16593887491681 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131268706187 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨32, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (16593887491681 / 20000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131268706187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_33 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82935216086171 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452508277063 / 20000000000000 : ℝ))
      (E := (cell12612 ⟨33, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82935216086171 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452508277063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_34 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41450509303597 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131272710961 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨34, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41450509303597 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131272710961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_35 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82866844990481 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131274703067 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨35, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82866844990481 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131274703067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_36 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82832695205197 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131276698707 / 50000000000000 : ℝ))
      (E := (cell12612 ⟨36, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82832695205197 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (1131276698707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_37 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (10349821152583 / 12500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (282819674553 / 12500000000000 : ℝ))
      (E := (cell12612 ⟨37, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (10349821152583 / 12500000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (282819674553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_38 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (82764467006359 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452512280721 / 20000000000000 : ℝ))
      (E := (cell12612 ⟨38, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (82764467006359 / 100000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (452512280721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12612_39 : CellCertificate 12612 (889165451246079 / 10000000000000000 : ℝ) (1665435846048003 / 1000000000000000000 : ℝ) (84116738356631 / 2500000000000000 : ℝ)
    (cell12612 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · norm_num [cell12612]
  · have h := gap_lower (n := 12612) (a := (41365194265957 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262565419173 / 100000000000000 : ℝ))
      (E := (cell12612 ⟨39, by decide⟩).energy) (xi := (84116738356631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12612 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12612]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12612])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12612) (a := (41365194265957 / 50000000000000 : ℝ)) (b := (2041687359 / 1250000000000 : ℝ)) (q := (2262565419173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12612])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12612]

theorem cert12613_20 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83381960143707 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262363418039 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨20, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83381960143707 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262363418039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_21 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83347449890861 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565591854419 / 25000000000000 : ℝ))
      (E := (cell12613 ⟨21, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83347449890861 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565591854419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_22 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (10414120489423 / 12500000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262371391769 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨22, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (10414120489423 / 12500000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262371391769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_23 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (20819625546079 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565593850637 / 25000000000000 : ℝ))
      (E := (cell12613 ⟨23, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (20819625546079 / 25000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565593850637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_24 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83244064664869 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262379395373 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨24, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83244064664869 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262379395373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_25 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (41604825662211 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (45247668641 / 2000000000000 : ℝ))
      (E := (cell12613 ⟨25, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (41604825662211 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (45247668641 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_26 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (41587631065261 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262387399011 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨26, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (41587631065261 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262387399011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_27 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (41570448525441 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262391416003 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨27, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (41570448525441 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262391416003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_28 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (4155327802669 / 5000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452479085471 / 20000000000000 : ℝ))
      (E := (cell12613 ⟨28, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (4155327802669 / 5000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (452479085471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_29 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83072239106059 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (70699982361 / 3125000000000 : ℝ))
      (E := (cell12613 ⟨29, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83072239106059 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (70699982361 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_30 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83037946177127 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131201721423 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨30, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83037946177127 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131201721423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_31 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (83003677234951 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262407451261 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨31, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (83003677234951 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262407451261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_32 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (41484716124031 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (56560285101 / 2500000000000 : ℝ))
      (E := (cell12613 ⟨32, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (41484716124031 / 50000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (56560285101 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_33 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82935211185151 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131207709913 / 50000000000000 : ℝ))
      (E := (cell12613 ⟨33, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82935211185151 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (1131207709913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_34 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82901014015067 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262419441433 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨34, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82901014015067 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262419441433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_35 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82866840706819 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565605852837 / 25000000000000 : ℝ))
      (E := (cell12613 ⟨35, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82866840706819 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (565605852837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_36 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82832691229573 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (3535042887 / 156250000000 : ℝ))
      (E := (cell12613 ⟨36, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82832691229573 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (3535042887 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_37 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82798565552651 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (70700982307 / 3125000000000 : ℝ))
      (E := (cell12613 ⟨37, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82798565552651 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (70700982307 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_38 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82764463645533 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262435428837 / 100000000000000 : ℝ))
      (E := (cell12613 ⟨38, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82764463645533 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (2262435428837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12613_39 : CellCertificate 12613 (889137141011227 / 10000000000000000 : ℝ) (1665303761119557 / 1000000000000000000 : ℝ) (168219808025817 / 5000000000000000 : ℝ)
    (cell12613 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · norm_num [cell12613]
  · have h := gap_lower (n := 12613) (a := (82730385477849 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (113121971647 / 5000000000000 : ℝ))
      (E := (cell12613 ⟨39, by decide⟩).energy) (xi := (168219808025817 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12613 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12613]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12613])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12613) (a := (82730385477849 / 100000000000000 : ℝ)) (b := (81660939253 / 50000000000000 : ℝ)) (q := (113121971647 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12613])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12613]

theorem cert12614_20 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (2605685974669 / 3125000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131118737421 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨20, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (2605685974669 / 3125000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131118737421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_21 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (5209215078191 / 6250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131120754249 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨21, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (5209215078191 / 6250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131120754249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_22 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (41656477794817 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262245517369 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨22, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (41656477794817 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262245517369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_23 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83278494172183 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262249505347 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨23, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83278494172183 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262249505347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_24 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (20811014241479 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262253476083 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨24, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (20811014241479 / 25000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262253476083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_25 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83209643938213 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262257491383 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨25, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83209643938213 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262257491383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_26 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83175255056621 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262261496089 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨26, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83175255056621 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262261496089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_27 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (16628178057771 / 20000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262265493147 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨27, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (16628178057771 / 20000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262265493147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_28 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83106549602793 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (565567371319 / 25000000000000 : ℝ))
      (E := (cell12614 ⟨28, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83106549602793 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (565567371319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_29 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (1038402912081 / 1250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131136737479 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨29, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (1038402912081 / 1250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131136737479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_30 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (41518970174061 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (45245550459 / 2000000000000 : ℝ))
      (E := (cell12614 ⟨30, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (41518970174061 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (45245550459 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_31 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (83003671716091 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262281514287 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨31, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (83003671716091 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262281514287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_32 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (16593885407783 / 20000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131142754623 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨32, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (16593885407783 / 20000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131142754623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_33 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (10366900785661 / 12500000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (226228950939 / 10000000000000 : ℝ))
      (E := (cell12614 ⟨33, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (10366900785661 / 12500000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (226228950939 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_34 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (4145050471203 / 5000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131146758029 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨34, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (4145050471203 / 5000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131146758029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_35 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (1035835455303 / 1250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262297530361 / 100000000000000 : ℝ))
      (E := (cell12614 ⟨35, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (1035835455303 / 1250000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (2262297530361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_36 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (41416343627497 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (113115074727 / 5000000000000 : ℝ))
      (E := (cell12614 ⟨36, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (41416343627497 / 50000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (113115074727 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_37 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82798561885647 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131152763261 / 50000000000000 : ℝ))
      (E := (cell12614 ⟨37, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82798561885647 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (1131152763261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_38 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82764460285677 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (282788688679 / 12500000000000 : ℝ))
      (E := (cell12614 ⟨38, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82764460285677 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (282788688679 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12614_39 : CellCertificate 12614 (889108835089193 / 10000000000000000 : ℝ) (832585848570317 / 500000000000000000 : ℝ) (42051535398553 / 1250000000000000 : ℝ)
    (cell12614 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · norm_num [cell12614]
  · have h := gap_lower (n := 12614) (a := (82730382424717 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (226231350213 / 10000000000000 : ℝ))
      (E := (cell12614 ⟨39, by decide⟩).energy) (xi := (42051535398553 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12614 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12614]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12614])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12614) (a := (82730382424717 / 100000000000000 : ℝ)) (b := (81654385207 / 50000000000000 : ℝ)) (q := (226231350213 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12614])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12614]

theorem cert12615_20 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83381942236763 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131055792943 / 50000000000000 : ℝ))
      (E := (cell12615 ⟨20, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83381942236763 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131055792943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_21 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41673716306433 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262115595329 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨21, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41673716306433 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262115595329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_22 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83312947265461 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262119580701 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨22, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83312947265461 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262119580701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_23 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83278486161589 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131061802117 / 50000000000000 : ℝ))
      (E := (cell12615 ⟨23, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83278486161589 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131061802117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_24 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (5202753079279 / 6250000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565531902821 / 25000000000000 : ℝ))
      (E := (cell12615 ⟨24, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (5202753079279 / 6250000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565531902821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_25 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41604818276733 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (226213160527 / 10000000000000 : ℝ))
      (E := (cell12615 ⟨25, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41604818276733 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (226213160527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_26 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (5198452999009 / 6250000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565533897343 / 25000000000000 : ℝ))
      (E := (cell12615 ⟨26, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (5198452999009 / 6250000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565533897343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_27 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83140883528213 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565534906243 / 25000000000000 : ℝ))
      (E := (cell12615 ⟨27, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83140883528213 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (565534906243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_28 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83106543153553 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (113107179897 / 5000000000000 : ℝ))
      (E := (cell12615 ⟨28, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83106543153553 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (113107179897 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_29 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83072226828209 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (45242952553 / 2000000000000 : ℝ))
      (E := (cell12615 ⟨29, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83072226828209 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (45242952553 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_30 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (83037934520389 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (452430319883 / 20000000000000 : ℝ))
      (E := (cell12615 ⟨30, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (83037934520389 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (452430319883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_31 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (1296932284351 / 1562500000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131077816121 / 50000000000000 : ℝ))
      (E := (cell12615 ⟨31, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (1296932284351 / 1562500000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (1131077816121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_32 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (16593884366193 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262159610891 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨32, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (16593884366193 / 20000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262159610891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_33 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (10366900173323 / 12500000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (282770449429 / 12500000000000 : ℝ))
      (E := (cell12615 ⟨33, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (10366900173323 / 12500000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (282770449429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_34 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (82901004834173 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262167645799 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨34, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (82901004834173 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262167645799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_35 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (82866832142743 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262171645929 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨35, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (82866832142743 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262171645929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_36 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (4141634164073 / 5000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262175596639 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨36, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (4141634164073 / 5000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262175596639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_37 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (1655971164393 / 2000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262179615853 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨37, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (1655971164393 / 2000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262179615853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_38 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (82764456926791 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262183645389 / 100000000000000 : ℝ))
      (E := (cell12615 ⟨38, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (82764456926791 / 100000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (2262183645389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12615_39 : CellCertificate 12615 (27783766671217 / 312500000000000 : ℝ) (266406344657 / 160000000000000 : ℝ) (168192477417837 / 5000000000000000 : ℝ)
    (cell12615 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · norm_num [cell12615]
  · have h := gap_lower (n := 12615) (a := (41365189686259 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (452437525349 / 20000000000000 : ℝ))
      (E := (cell12615 ⟨39, by decide⟩).energy) (xi := (168192477417837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12615 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12615]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12615])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12615) (a := (41365189686259 / 50000000000000 : ℝ)) (b := (163295664443 / 100000000000000 : ℝ)) (q := (452437525349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12615])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12615]

theorem cert12616_20 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (8338193328577 / 10000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261985751171 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨20, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (8338193328577 / 10000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261985751171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_21 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83347423976291 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261989736463 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨21, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83347423976291 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261989736463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_22 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (5207058683929 / 6250000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261993756717 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨22, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (5207058683929 / 6250000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261993756717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_23 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (20819619538133 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261997757551 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨23, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (20819619538133 / 25000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2261997757551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_24 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83244041572511 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131000871307 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨24, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83244041572511 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131000871307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_25 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (4160481458509 / 5000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (141375360857 / 6250000000000 : ℝ))
      (E := (cell12616 ⟨25, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (4160481458509 / 5000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (141375360857 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_26 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (8317524091309 / 10000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262009737273 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨26, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (8317524091309 / 10000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262009737273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_27 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83140876768957 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262013753041 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨27, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83140876768957 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262013753041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_28 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83106536705661 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (70688055167 / 3125000000000 : ℝ))
      (E := (cell12616 ⟨28, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83106536705661 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (70688055167 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_29 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (5192013793203 / 6250000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (282752722083 / 12500000000000 : ℝ))
      (E := (cell12616 ⟨29, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (5192013793203 / 6250000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (282752722083 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_30 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (10379741086741 / 12500000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262025789251 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨30, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (10379741086741 / 12500000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262025789251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_31 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (83003660682071 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262029746597 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨31, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (83003660682071 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262029746597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_32 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82969416624209 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262033767529 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨32, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82969416624209 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262033767529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_33 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82935196489037 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262037795103 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨33, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82935196489037 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262037795103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_34 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82901000245407 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262041772057 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨34, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82901000245407 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262041772057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_35 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82866827862329 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262045758053 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨35, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82866827862329 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262045758053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_36 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82832679308971 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262049753977 / 100000000000000 : ℝ))
      (E := (cell12616 ⟨36, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82832679308971 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (2262049753977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_37 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (4139927727733 / 5000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131026880243 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨37, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (4139927727733 / 5000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131026880243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_38 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (662115628551 / 800000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131028889009 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨38, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (662115628551 / 800000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131028889009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12616_39 : CellCertificate 12616 (889052236179447 / 10000000000000000 : ℝ) (1664907632011423 / 1000000000000000000 : ℝ) (2102235193701 / 62500000000000 : ℝ)
    (cell12616 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · norm_num [cell12616]
  · have h := gap_lower (n := 12616) (a := (82730376321251 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131030903393 / 50000000000000 : ℝ))
      (E := (cell12616 ⟨39, by decide⟩).energy) (xi := (2102235193701 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12616 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12616]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12616])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12616) (a := (82730376321251 / 100000000000000 : ℝ)) (b := (163282560593 / 100000000000000 : ℝ)) (q := (1131030903393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12616])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12616]

theorem cert12617_20 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83381924336431 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261859970699 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨20, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83381924336431 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261859970699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_21 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (8334741534133 / 10000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (452372786381 / 20000000000000 : ℝ))
      (E := (cell12617 ⟨21, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (8334741534133 / 10000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (452372786381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_22 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83312930621843 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (452373585757 / 20000000000000 : ℝ))
      (E := (cell12617 ⟨22, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83312930621843 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (452373585757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_23 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83278470145013 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261871965299 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨23, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83278470145013 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261871965299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_24 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83244033878057 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130937964219 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨24, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83244033878057 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130937964219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_25 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (20802405447089 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261879938323 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨25, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (20802405447089 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261879938323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_26 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (4158761692173 / 5000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (141367746237 / 6250000000000 : ℝ))
      (E := (cell12617 ⟨26, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (4158761692173 / 5000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (141367746237 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_27 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (41570435005543 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (141367995987 / 6250000000000 : ℝ))
      (E := (cell12617 ⟨27, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (41570435005543 / 50000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (141367995987 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_28 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (20776632564779 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (565472982259 / 25000000000000 : ℝ))
      (E := (cell12617 ⟨28, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (20776632564779 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (565472982259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_29 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (20768053638899 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130947990243 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨29, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (20768053638899 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130947990243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_30 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (83037922868737 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261899975453 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨30, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (83037922868737 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261899975453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_31 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (8300365516691 / 10000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130951987207 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨31, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (8300365516691 / 10000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130951987207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_32 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (82969411418649 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (56547699479 / 2500000000000 : ℝ))
      (E := (cell12617 ⟨32, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (82969411418649 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (56547699479 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_33 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (10366898949081 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130955995627 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨33, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (10366898949081 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130955995627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_34 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (518131222861 / 625000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130957976717 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨34, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (518131222861 / 625000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130957976717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_35 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (20716705895749 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261919983981 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨35, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (20716705895749 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261919983981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_36 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (82832675337527 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130961983279 / 50000000000000 : ℝ))
      (E := (cell12617 ⟨36, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (82832675337527 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (1130961983279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_37 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (82798550890677 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (282740995053 / 12500000000000 : ℝ))
      (E := (cell12617 ⟨37, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (82798550890677 / 100000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (282740995053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_38 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (10345556276491 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261931966013 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨38, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (10345556276491 / 12500000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261931966013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12617_39 : CellCertificate 12617 (88902394318967 / 1000000000000000 : ℝ) (416193907712793 / 250000000000000000 : ℝ) (168165155828331 / 5000000000000000 : ℝ)
    (cell12617 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · norm_num [cell12617]
  · have h := gap_lower (n := 12617) (a := (20682593317729 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261935983539 / 100000000000000 : ℝ))
      (E := (cell12617 ⟨39, by decide⟩).energy) (xi := (168165155828331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12617 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12617]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12617])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12617) (a := (20682593317729 / 25000000000000 : ℝ)) (b := (81634729431 / 50000000000000 : ℝ)) (q := (2261935983539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12617])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12617]

theorem cert12618_20 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83381915388743 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130867093101 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨20, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83381915388743 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130867093101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_21 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83347406707983 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565434545413 / 25000000000000 : ℝ))
      (E := (cell12618 ⟨21, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83347406707983 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565434545413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_22 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83312922302397 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130871077611 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨22, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83312922302397 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130871077611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_23 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (10409807767379 / 12500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130873084569 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨23, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (10409807767379 / 12500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130873084569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_24 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41622013092551 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261750168757 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨24, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41622013092551 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261750168757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_25 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83209614407991 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565438539373 / 25000000000000 : ℝ))
      (E := (cell12618 ⟨25, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83209614407991 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (565438539373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_26 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83175226775251 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261758196933 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨26, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83175226775251 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261758196933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_27 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83140863254599 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130881086613 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨27, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83140863254599 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130881086613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_28 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83106523813917 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261766205931 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨28, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83106523813917 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261766205931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_29 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (20768052105313 / 25000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130885090317 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨29, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (20768052105313 / 25000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130885090317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_30 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (83037917044817 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261774216523 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨30, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (83037917044817 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261774216523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_31 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41501824826491 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261778198633 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨31, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41501824826491 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261778198633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_32 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (20742351553571 / 25000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261782187233 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨32, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (20742351553571 / 25000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261782187233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_33 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (10366898337177 / 12500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261786183887 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨33, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (10366898337177 / 12500000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261786183887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_34 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (80957999093 / 97656250000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261790189929 / 100000000000000 : ℝ))
      (E := (cell12618 ⟨34, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (80957999093 / 97656250000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (2261790189929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_35 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (41433409652373 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130897103233 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨35, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (41433409652373 / 50000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130897103233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_36 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82832671367127 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452359635147 / 20000000000000 : ℝ))
      (E := (cell12618 ⟨36, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82832671367127 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452359635147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_37 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82798547227701 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452360443133 / 20000000000000 : ℝ))
      (E := (cell12618 ⟨37, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82798547227701 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (452360443133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_38 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82764446855951 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130903104687 / 50000000000000 : ℝ))
      (E := (cell12618 ⟨38, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82764446855951 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (1130903104687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12618_39 : CellCertificate 12618 (444497827254291 / 5000000000000000 : ℝ) (1664643650620519 / 1000000000000000000 : ℝ) (336302996827959 / 10000000000000000 : ℝ)
    (cell12618 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · norm_num [cell12618]
  · have h := gap_lower (n := 12618) (a := (82730370221513 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (56545255393 / 2500000000000 : ℝ))
      (E := (cell12618 ⟨39, by decide⟩).energy) (xi := (336302996827959 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12618 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12618]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12618])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12618) (a := (82730370221513 / 100000000000000 : ℝ)) (b := (163256359251 / 100000000000000 : ℝ)) (q := (56545255393 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12618])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12618]

theorem cert12619_20 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (20845476610677 / 25000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261608455949 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨20, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (20845476610677 / 25000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261608455949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_21 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83347398076249 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452322485483 / 20000000000000 : ℝ))
      (E := (cell12619 ⟨21, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83347398076249 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452322485483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_22 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (41656456992263 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261616436031 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨22, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (41656456992263 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261616436031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_23 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83278454134587 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565405106853 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨23, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83278454134587 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565405106853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_24 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (16648803698729 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261624463573 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨24, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (16648803698729 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261624463573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_25 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (2600300219659 / 3125000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (113081421561 / 5000000000000 : ℝ))
      (E := (cell12619 ⟨25, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (2600300219659 / 3125000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (113081421561 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_26 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (16635043941693 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565408112571 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨26, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (16635043941693 / 20000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565408112571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_27 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (10392607062437 / 12500000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452327293069 / 20000000000000 : ℝ))
      (E := (cell12619 ⟨27, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (10392607062437 / 12500000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452327293069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_28 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (5194157335629 / 6250000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452328095823 / 20000000000000 : ℝ))
      (E := (cell12619 ⟨28, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (5194157335629 / 6250000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (452328095823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_29 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83072202288217 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261644435591 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨29, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83072202288217 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261644435591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_30 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83037911222167 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261648453961 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨30, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83037911222167 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261648453961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_31 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (83003644140287 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130826238893 / 50000000000000 : ℝ))
      (E := (cell12619 ⟨31, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (83003644140287 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (1130826238893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_32 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82969401011113 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261656450303 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨32, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82969401011113 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261656450303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_33 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82935181803341 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261660490153 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨33, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82935181803341 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261660490153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_34 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (1295327913841 / 1562500000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (282708060193 / 12500000000000 : ℝ))
      (E := (cell12619 ⟨34, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (1295327913841 / 1562500000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (282708060193 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_35 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82866815027577 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261668484133 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨35, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82866815027577 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261668484133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_36 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (8283266739777 / 10000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565418124701 / 25000000000000 : ℝ))
      (E := (cell12619 ⟨36, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (8283266739777 / 10000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (565418124701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_37 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82798543565731 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (282709558443 / 12500000000000 : ℝ))
      (E := (cell12619 ⟨37, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82798543565731 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (282709558443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_38 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (41382221750471 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261680449411 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨38, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (41382221750471 / 50000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261680449411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12619_39 : CellCertificate 12619 (55560460633447 / 625000000000000 : ℝ) (832255845657243 / 500000000000000000 : ℝ) (33627568650483 / 1000000000000000 : ℝ)
    (cell12619 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · norm_num [cell12619]
  · have h := gap_lower (n := 12619) (a := (82730367173041 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261684503331 / 100000000000000 : ℝ))
      (E := (cell12619 ⟨39, by decide⟩).energy) (xi := (33627568650483 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12619 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12619]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12619])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12619) (a := (82730367173041 / 100000000000000 : ℝ)) (b := (81621630879 / 50000000000000 : ℝ)) (q := (2261684503331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12619])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12619]

theorem cert12620_20 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83381897498323 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261482779943 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨20, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83381897498323 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261482779943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_21 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (5209211840383 / 6250000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (113074339289 / 5000000000000 : ℝ))
      (E := (cell12620 ⟨21, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (5209211840383 / 6250000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (113074339289 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_22 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (8331290566823 / 10000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261490771211 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨22, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (8331290566823 / 10000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261490771211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_23 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41639223065839 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (56537368503 / 2500000000000 : ℝ))
      (E := (cell12620 ⟨23, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41639223065839 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (56537368503 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_24 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83244010803687 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261498754521 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨24, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83244010803687 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261498754521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_25 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (20802399912911 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261502759507 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨25, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (20802399912911 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261502759507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_26 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (831752126431 / 1000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130753379129 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨26, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (831752126431 / 1000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130753379129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_27 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (5196303109111 / 6250000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130755376857 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨27, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (5196303109111 / 6250000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130755376857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_28 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (20776627731889 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565378687147 / 25000000000000 : ℝ))
      (E := (cell12620 ⟨28, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (20776627731889 / 25000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (565378687147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_29 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (83072196156489 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261518745357 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨29, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (83072196156489 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261518745357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_30 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41518952700393 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261522746271 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨30, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41518952700393 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261522746271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_31 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (10375454828603 / 12500000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (35336355521 / 1562500000000 : ℝ))
      (E := (cell12620 ⟨31, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (10375454828603 / 12500000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (35336355521 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_32 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82969395809137 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (141345673023 / 6250000000000 : ℝ))
      (E := (cell12620 ⟨32, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82969395809137 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (141345673023 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_33 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41467588455211 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130767396451 / 50000000000000 : ℝ))
      (E := (cell12620 ⟨33, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41467588455211 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (1130767396451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_34 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41450490950767 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (28269234621 / 1250000000000 : ℝ))
      (E := (cell12620 ⟨34, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41450490950767 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (28269234621 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_35 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82866810751489 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (56538568959 / 2500000000000 : ℝ))
      (E := (cell12620 ⟨35, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82866810751489 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (56538568959 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_36 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82832663429457 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (90461870393 / 4000000000000 : ℝ))
      (E := (cell12620 ⟨36, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82832663429457 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (90461870393 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_37 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82798539904767 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (226155077473 / 10000000000000 : ℝ))
      (E := (cell12620 ⟨37, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82798539904767 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (226155077473 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_38 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (41382220073451 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261554803509 / 100000000000000 : ℝ))
      (E := (cell12620 ⟨38, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (41382220073451 / 50000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (2261554803509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12620_39 : CellCertificate 12620 (222234772517087 / 2500000000000000 : ℝ) (1664379752928097 / 1000000000000000000 : ℝ) (42031047585757 / 1250000000000000 : ℝ)
    (cell12620 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · norm_num [cell12620]
  · have h := gap_lower (n := 12620) (a := (82730364125501 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452311757531 / 20000000000000 : ℝ))
      (E := (cell12620 ⟨39, by decide⟩).energy) (xi := (42031047585757 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12620 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12620]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12620])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12620) (a := (82730364125501 / 100000000000000 : ℝ)) (b := (10201885399 / 6250000000000 : ℝ)) (q := (452311757531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12620])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12620]

theorem cert12621_20 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (8338188855559 / 10000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261357099913 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨20, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (8338188855559 / 10000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261357099913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_21 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (4167369040881 / 5000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261361140161 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨21, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (4167369040881 / 5000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261361140161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_22 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (83312897353509 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130682551223 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨22, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (83312897353509 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130682551223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_23 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (16655687626061 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (35333892301 / 1562500000000 : ℝ))
      (E := (cell12621 ⟨23, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (16655687626061 / 20000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (35333892301 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_24 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41622001557613 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (35333954687 / 1562500000000 : ℝ))
      (E := (cell12621 ⟨24, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41622001557613 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (35333954687 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_25 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (83209592275659 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565344285589 / 25000000000000 : ℝ))
      (E := (cell12621 ⟨25, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (83209592275659 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565344285589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_26 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (83175205579157 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130690560427 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨26, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (83175205579157 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130690560427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_27 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (519630268709 / 625000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (35334142137 / 1562500000000 : ℝ))
      (E := (cell12621 ⟨27, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (519630268709 / 625000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (35334142137 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_28 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41553252243197 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130694565633 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨28, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41553252243197 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130694565633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_29 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (20768047506517 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130696554967 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨29, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (20768047506517 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130696554967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_30 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (20759474895169 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565349273363 / 25000000000000 : ℝ))
      (E := (cell12621 ⟨30, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (20759474895169 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (565349273363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_31 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (648465883739 / 781250000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261401142367 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨31, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (648465883739 / 781250000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261401142367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_32 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41484695304177 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261405141431 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨32, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41484695304177 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261405141431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_33 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82935172018659 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261409150711 / 100000000000000 : ℝ))
      (E := (cell12621 ⟨33, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82935172018659 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (2261409150711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_34 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82900977318363 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130706556469 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨34, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82900977318363 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130706556469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_35 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (41433403238241 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130708573197 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨35, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (41433403238241 / 50000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130708573197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_36 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (20708164865547 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (141338820921 / 6250000000000 : ℝ))
      (E := (cell12621 ⟨36, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (20708164865547 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (141338820921 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_37 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82798536244809 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130712568611 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨37, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82798536244809 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130712568611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_38 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (82764436793831 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130714577141 / 50000000000000 : ℝ))
      (E := (cell12621 ⟨38, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (82764436793831 / 100000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (1130714577141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12621_39 : CellCertificate 12621 (888910814307139 / 10000000000000000 : ℝ) (832123917728189 / 500000000000000000 : ℝ) (336221079370417 / 10000000000000000 : ℝ)
    (cell12621 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · norm_num [cell12621]
  · have h := gap_lower (n := 12621) (a := (20682590269723 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (226143312741 / 10000000000000 : ℝ))
      (E := (cell12621 ⟨39, by decide⟩).energy) (xi := (336221079370417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12621 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12621]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12621])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12621) (a := (20682590269723 / 25000000000000 : ℝ)) (b := (20402134141 / 12500000000000 : ℝ)) (q := (226143312741 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12621])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12621]

theorem cert12622_20 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83381879614507 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261231474133 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨20, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83381879614507 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261231474133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_21 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20836843047681 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261235490561 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨21, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20836843047681 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261235490561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_22 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83312889040361 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261239488057 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨22, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83312889040361 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261239488057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_23 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20819607532617 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130621764423 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨23, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20819607532617 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130621764423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_24 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83243995428263 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452249499983 / 20000000000000 : ℝ))
      (E := (cell12622 ⟨24, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83243995428263 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452249499983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_25 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41604792450567 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (113062576069 / 5000000000000 : ℝ))
      (E := (cell12622 ⟨25, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41604792450567 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (113062576069 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_26 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (16635039703327 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452251095933 / 20000000000000 : ℝ))
      (E := (cell12622 ⟨26, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (16635039703327 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452251095933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_27 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (10392604530311 / 12500000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (226125949451 / 10000000000000 : ℝ))
      (E := (cell12622 ⟨27, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (10392604530311 / 12500000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (226125949451 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_28 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83106498046577 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130631755119 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨28, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83106498046577 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130631755119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_29 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (16614436779391 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565316882331 / 25000000000000 : ℝ))
      (E := (cell12622 ⟨29, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (16614436779391 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (565316882331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_30 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (41518946880917 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (226127149551 / 10000000000000 : ℝ))
      (E := (cell12622 ⟨30, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (41518946880917 / 50000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (226127149551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_31 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (83003627609591 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261275527799 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨31, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (83003627609591 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261275527799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_32 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (16593877081753 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130639755471 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨32, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (16593877081753 / 20000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130639755471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_33 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20733791782013 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130641752503 / 50000000000000 : ℝ))
      (E := (cell12622 ⟨33, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20733791782013 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (1130641752503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_34 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (8290097273631 / 10000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261287511321 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨34, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (8290097273631 / 10000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261287511321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_35 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (20716700550639 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (226129153099 / 10000000000000 : ℝ))
      (E := (cell12622 ⟨35, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (20716700550639 / 25000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (226129153099 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_36 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82832655495961 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261295506251 / 100000000000000 : ℝ))
      (E := (cell12622 ⟨36, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82832655495961 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (2261295506251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_37 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82798532585857 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452259899271 / 20000000000000 : ℝ))
      (E := (cell12622 ⟨37, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82798532585857 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (452259899271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_38 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82764433441727 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (282662937717 / 12500000000000 : ℝ))
      (E := (cell12622 ⟨38, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82764433441727 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (282662937717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12622_39 : CellCertificate 12622 (177776508570099 / 2000000000000000 : ℝ) (1664115938894357 / 1000000000000000000 : ℝ) (42024222819587 / 1250000000000000 : ℝ)
    (cell12622 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · norm_num [cell12622]
  · have h := gap_lower (n := 12622) (a := (82730358033213 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (11306537613 / 500000000000 : ℝ))
      (E := (cell12622 ⟨39, by decide⟩).energy) (xi := (42024222819587 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12622 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12622]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12622])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12622) (a := (82730358033213 / 100000000000000 : ℝ)) (b := (40800995497 / 25000000000000 : ℝ)) (q := (11306537613 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12622])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12622]

theorem cert12623_20 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (3335274827003 / 4000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261105902601 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨20, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (3335274827003 / 4000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261105902601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_21 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83347363565439 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261109953567 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨21, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83347363565439 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261109953567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_22 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41656440364393 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261113928043 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨22, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41656440364393 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261113928043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_23 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (16655684426433 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565279486631 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨23, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (16655684426433 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565279486631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_24 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83243987742797 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261121954361 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨24, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83243987742797 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261121954361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_25 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (20802394382017 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130562977483 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨25, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (20802394382017 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130562977483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_26 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41587595727767 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (282641243939 / 12500000000000 : ℝ))
      (E := (cell12623 ⟨26, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41587595727767 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (282641243939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_27 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83140829492917 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261133946941 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨27, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83140829492917 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261133946941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_28 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (16621298321621 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261137943959 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨28, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (16621298321621 / 20000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261137943959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_29 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (20768044442287 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565285486261 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨29, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (20768044442287 / 25000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565285486261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_30 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (83037887944261 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130572976221 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨30, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (83037887944261 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130572976221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_31 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (41501811050911 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130574984083 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨31, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (41501811050911 / 50000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130574984083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_32 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82969380210369 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565288483863 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨32, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82969380210369 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565288483863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_33 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82935162238601 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261157972937 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨33, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82935162238601 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261157972937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_34 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (663207745243 / 800000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130580982413 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨34, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (663207745243 / 800000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130580982413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_35 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (8286679792971 / 10000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565291492693 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨35, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (8286679792971 / 10000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565291492693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_36 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82832651530777 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565292483253 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨36, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82832651530777 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565292483253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_37 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82798528927909 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261173969467 / 100000000000000 : ℝ))
      (E := (cell12623 ⟨37, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82798528927909 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (2261173969467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_38 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (82764430090591 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565294490813 / 25000000000000 : ℝ))
      (E := (cell12623 ⟨38, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (82764430090591 / 100000000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (565294490813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12623_39 : CellCertificate 12623 (444427137848693 / 5000000000000000 : ℝ) (1663984063237063 / 1000000000000000000 : ℝ) (168083245121837 / 5000000000000000 : ℝ)
    (cell12623 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · norm_num [cell12623]
  · have h := gap_lower (n := 12623) (a := (5170647186779 / 6250000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130590986611 / 50000000000000 : ℝ))
      (E := (cell12623 ⟨39, by decide⟩).energy) (xi := (168083245121837 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12623 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12623]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12623])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12623) (a := (5170647186779 / 6250000000000 : ℝ)) (b := (81595446483 / 50000000000000 : ℝ)) (q := (1130590986611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12623])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12623]

theorem cert12624_20 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (20845465434323 / 25000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260980385323 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨20, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (20845465434323 / 25000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260980385323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_21 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41673677470883 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260984412593 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨21, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41673677470883 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260984412593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_22 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (16662574483757 / 20000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (452197684481 / 20000000000000 : ℝ))
      (E := (cell12624 ⟨22, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (16662574483757 / 20000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (452197684481 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_23 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41639207067699 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130496209321 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨23, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41639207067699 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130496209321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_24 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83243980058827 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260996404947 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨24, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83243980058827 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2260996404947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_25 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (4160478507823 / 5000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (226100038473 / 10000000000000 : ℝ))
      (E := (cell12624 ⟨25, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (4160478507823 / 5000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (226100038473 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_26 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83175184395853 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (282625552447 / 12500000000000 : ℝ))
      (E := (cell12624 ⟨26, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83175184395853 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (282625552447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_27 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83140822744729 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130504197813 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨27, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83140822744729 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130504197813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_28 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (2597077661593 / 3125000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130506216217 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨28, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (2597077661593 / 3125000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130506216217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_29 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83072171642647 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (113050820779 / 5000000000000 : ℝ))
      (E := (cell12624 ⟨29, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83072171642647 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (113050820779 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_30 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83037882127957 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130510202873 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨30, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83037882127957 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130510202873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_31 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (83003616595283 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130512202473 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨31, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (83003616595283 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130512202473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_32 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41484687506583 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261028414963 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨32, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41484687506583 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261028414963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_33 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (2591723667197 / 3125000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130516218679 / 50000000000000 : ℝ))
      (E := (cell12624 ⟨33, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (2591723667197 / 3125000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (1130516218679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_34 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41450481787779 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261036414857 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨34, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41450481787779 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261036414857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_35 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82866793657943 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (28263005089 / 1250000000000 : ℝ))
      (E := (cell12624 ⟨35, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82866793657943 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (28263005089 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_36 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (20708161891659 / 25000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261044415023 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨36, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (20708161891659 / 25000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261044415023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_37 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82798525270967 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261048439221 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨37, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82798525270967 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261048439221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_38 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (82764426740423 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (45221048429 / 2000000000000 : ℝ))
      (E := (cell12624 ⟨38, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (82764426740423 / 100000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (45221048429 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

theorem cert12624_39 : CellCertificate 12624 (888826012846783 / 10000000000000000 : ℝ) (66554088339181 / 40000000000000000 : ℝ) (336139202430133 / 10000000000000000 : ℝ)
    (cell12624 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · norm_num [cell12624]
  · have h := gap_lower (n := 12624) (a := (41365175972323 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261056420563 / 100000000000000 : ℝ))
      (E := (cell12624 ⟨39, by decide⟩).energy) (xi := (336139202430133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12624 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12624]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12624])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12624) (a := (41365175972323 / 50000000000000 : ℝ)) (b := (163177806059 / 100000000000000 : ℝ)) (q := (2261056420563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12624])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12624]

end BstLean.Part268
