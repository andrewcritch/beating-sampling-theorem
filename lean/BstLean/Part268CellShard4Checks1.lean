import BstLean.Part268CellShard4Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12450_20 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83383442109137 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283477783301 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨20, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83383442109137 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283477783301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_21 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (16669776014799 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283481809099 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨21, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (16669776014799 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283481809099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_22 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83314342388539 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285435725623 / 12500000000000 : ℝ))
      (E := (cell12450 ⟨22, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83314342388539 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285435725623 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_23 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83279829019663 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285436221891 / 12500000000000 : ℝ))
      (E := (cell12450 ⟨23, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83279829019663 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285436221891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_24 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83245339934433 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283493781809 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨24, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83245339934433 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283493781809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_25 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41605437550043 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (91339910817 / 4000000000000 : ℝ))
      (E := (cell12450 ⟨25, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41605437550043 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (91339910817 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_26 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41588217242013 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283501802827 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨26, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41588217242013 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283501802827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_27 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41571009026913 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283505765477 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨27, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41571009026913 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283505765477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_28 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (41553812888611 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283509778179 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨28, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (41553812888611 / 50000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283509778179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_29 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83073257622119 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (456702757059 / 20000000000000 : ℝ))
      (E := (cell12450 ⟨29, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83073257622119 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (456702757059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_30 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (16607782711317 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283517789353 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨30, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (16607782711317 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283517789353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_31 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (83004593548851 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283521792647 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨31, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (83004593548851 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283521792647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_32 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82970297567311 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570881449311 / 25000000000000 : ℝ))
      (E := (cell12450 ⟨32, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82970297567311 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570881449311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_33 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82936025580519 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283529746421 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨33, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82936025580519 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283529746421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_34 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (10362722194649 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141766879439 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨34, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (10362722194649 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141766879439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_35 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82867553466203 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285442222183 / 12500000000000 : ℝ))
      (E := (cell12450 ⟨35, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82867553466203 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (285442222183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_36 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (16566670655317 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283541744703 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨36, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (16566670655317 / 20000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283541744703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_37 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82799176957529 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141772889379 / 50000000000000 : ℝ))
      (E := (cell12450 ⟨37, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82799176957529 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (1141772889379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_38 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (82765024478383 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570887440763 / 25000000000000 : ℝ))
      (E := (cell12450 ⟨38, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (82765024478383 / 100000000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (570887440763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12450_39 : CellCertificate 12450 (55863087934359 / 625000000000000 : ℝ) (843556922874069 / 500000000000000000 : ℝ) (34095607564311 / 1000000000000000 : ℝ)
    (cell12450 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · norm_num [cell12450]
  · have h := gap_lower (n := 12450) (a := (10341361976081 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283553756697 / 100000000000000 : ℝ))
      (E := (cell12450 ⟨39, by decide⟩).energy) (xi := (34095607564311 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12450 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12450]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12450])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12450) (a := (10341361976081 / 12500000000000 : ℝ)) (b := (33097450157 / 20000000000000 : ℝ)) (q := (2283553756697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12450])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12450]

theorem cert12451_20 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83383432879583 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283344297471 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨20, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83383432879583 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283344297471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_21 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83348871165309 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570837072289 / 25000000000000 : ℝ))
      (E := (cell12451 ⟨21, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83348871165309 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (570837072289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_22 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (5207145862517 / 6250000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283352309951 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨22, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (5207145862517 / 6250000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283352309951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_23 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (10409977593921 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141678152887 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨23, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (10409977593921 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141678152887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_24 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (325177078069 / 390625000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283360280557 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨24, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (325177078069 / 390625000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283360280557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_25 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (20802716867599 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141682148183 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨25, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (20802716867599 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141682148183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_26 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83176427172971 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456673659667 / 20000000000000 : ℝ))
      (E := (cell12451 ⟨26, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83176427172971 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456673659667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_27 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83142011060961 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283372289689 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨27, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83142011060961 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283372289689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_28 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (16621523820421 / 20000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141688136709 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨28, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (16621523820421 / 20000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141688136709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_29 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (20768312816077 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285422538843 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨29, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (20768312816077 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285422538843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_30 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41519453757819 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285423035911 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨30, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41519453757819 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285423035911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_31 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (83004587824327 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456677652757 / 20000000000000 : ℝ))
      (E := (cell12451 ⟨31, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (83004587824327 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456677652757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_32 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (82970292158771 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141696150417 / 50000000000000 : ℝ))
      (E := (cell12451 ⟨32, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (82970292158771 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (1141696150417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_33 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (20734005121881 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285424535403 / 12500000000000 : ℝ))
      (E := (cell12451 ⟨33, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (20734005121881 / 25000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (285424535403 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_34 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (82901772779303 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (91336010843 / 4000000000000 : ℝ))
      (E := (cell12451 ⟨34, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (82901772779303 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (91336010843 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_35 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (10358443625373 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456680853153 / 20000000000000 : ℝ))
      (E := (cell12451 ⟨35, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (10358443625373 / 12500000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456680853153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_36 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (207083372819 / 250000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (45668165369 / 2000000000000 : ℝ))
      (E := (cell12451 ⟨36, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (207083372819 / 250000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (45668165369 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_37 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41399586561171 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283412280057 / 100000000000000 : ℝ))
      (E := (cell12451 ⟨37, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41399586561171 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (2283412280057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_38 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (82765020956559 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456683248523 / 20000000000000 : ℝ))
      (E := (cell12451 ⟨38, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (82765020956559 / 100000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (456683248523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12451_39 : CellCertificate 12451 (279306370049 / 3125000000000 : ℝ) (337395660007483 / 200000000000000000 : ℝ) (340927990810691 / 10000000000000000 : ℝ)
    (cell12451 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · norm_num [cell12451]
  · have h := gap_lower (n := 12451) (a := (41365446299877 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (228342027393 / 10000000000000 : ℝ))
      (E := (cell12451 ⟨39, by decide⟩).energy) (xi := (340927990810691 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12451 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12451]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12451])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12451) (a := (41365446299877 / 50000000000000 : ℝ)) (b := (10342111849 / 6250000000000 : ℝ)) (q := (228342027393 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12451])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12451]

theorem cert12452_20 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83383423651753 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141605432837 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨20, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83383423651753 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141605432837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_21 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (20837215564577 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141607440793 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨21, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (20837215564577 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141607440793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_22 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (1666286504273 / 2000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283218869079 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨22, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (1666286504273 / 2000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283218869079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_23 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41639906242339 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283222832323 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨23, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41639906242339 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283222832323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_24 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83245324038459 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570806708399 / 25000000000000 : ℝ))
      (E := (cell12452 ⟨24, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83245324038459 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570806708399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_25 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (10401357480279 / 12500000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283230876661 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨25, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (10401357480279 / 12500000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283230876661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_26 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41588209931701 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283234848261 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨26, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41588209931701 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283234848261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_27 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83142004069543 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141619434191 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨27, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83142004069543 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141619434191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_28 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (20776903107099 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283242823203 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨28, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (20776903107099 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283242823203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_29 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (10384155613483 / 12500000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283246832339 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨29, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (10384155613483 / 12500000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283246832339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_30 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83038901476019 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283250839897 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨30, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83038901476019 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283250839897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_31 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (83004582101093 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283254848171 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨31, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (83004582101093 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283254848171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_32 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82970286751481 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (285407357403 / 12500000000000 : ℝ))
      (E := (cell12452 ⟨32, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82970286751481 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (285407357403 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_33 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82936015395741 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283262816333 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨33, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82936015395741 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283262816333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_34 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (20725442000647 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141633419099 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨34, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (20725442000647 / 25000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141633419099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_35 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82867544540899 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141635404529 / 50000000000000 : ℝ))
      (E := (cell12452 ⟨35, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82867544540899 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (1141635404529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_36 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (8283334497971 / 10000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570818711813 / 25000000000000 : ℝ))
      (E := (cell12452 ⟨36, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (8283334497971 / 10000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (570818711813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_37 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82799169288211 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (91331153459 / 4000000000000 : ℝ))
      (E := (cell12452 ⟨37, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82799169288211 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (91331153459 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_38 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (82765017435753 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283282836033 / 100000000000000 : ℝ))
      (E := (cell12452 ⟨38, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (82765017435753 / 100000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (2283282836033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12452_39 : CellCertificate 12452 (223437841462127 / 2500000000000000 : ℝ) (210855347013113 / 125000000000000000 : ℝ) (42612488836981 / 1250000000000000 : ℝ)
    (cell12452 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · norm_num [cell12452]
  · have h := gap_lower (n := 12452) (a := (41365444695919 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (285410855801 / 12500000000000 : ℝ))
      (E := (cell12452 ⟨39, by decide⟩).energy) (xi := (42612488836981 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12452 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12452]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12452])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12452) (a := (41365444695919 / 50000000000000 : ℝ)) (b := (33092066119 / 20000000000000 : ℝ)) (q := (285410855801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12452])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12452]

theorem cert12453_20 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83383414425647 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (285384685989 / 12500000000000 : ℝ))
      (E := (cell12453 ⟨20, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83383414425647 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (285384685989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_21 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (8334885335299 / 10000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283081469839 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨21, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (8334885335299 / 10000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283081469839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_22 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (1301786197323 / 1562500000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283085482371 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨22, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (1301786197323 / 1562500000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283085482371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_23 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83279804219593 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283089471423 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨23, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83279804219593 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283089471423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_24 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (4162265804641 / 5000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283093499273 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨24, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (4162265804641 / 5000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283093499273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_25 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83210852215593 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141548726471 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨25, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83210852215593 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141548726471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_26 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83176412555319 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141550726303 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨26, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83176412555319 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141550726303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_27 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (20785499269893 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283105443141 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨27, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (20785499269893 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283105443141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_28 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41553802878047 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (285388685747 / 12500000000000 : ℝ))
      (E := (cell12453 ⟨28, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41553802878047 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (285388685747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_29 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83073238552789 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283113467009 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨29, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83073238552789 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283113467009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_30 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (8303889543773 / 10000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (114155872359 / 5000000000000 : ℝ))
      (E := (cell12453 ⟨30, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (8303889543773 / 10000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (114155872359 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_31 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (83004576379149 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456624297459 / 20000000000000 : ℝ))
      (E := (cell12453 ⟨31, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (83004576379149 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (456624297459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_32 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41485140672721 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283125472417 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨32, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41485140672721 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283125472417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_33 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82936010305169 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141564731433 / 50000000000000 : ℝ))
      (E := (cell12453 ⟨33, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82936010305169 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (1141564731433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_34 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (16580352645409 / 20000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (9132533841 / 400000000000 : ℝ))
      (E := (cell12453 ⟨34, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (16580352645409 / 20000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (9132533841 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_35 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (20716885019987 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570784366487 / 25000000000000 : ℝ))
      (E := (cell12453 ⟨35, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (20716885019987 / 25000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570784366487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_36 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (41416670416457 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (228314148111 / 10000000000000 : ℝ))
      (E := (cell12453 ⟨36, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (41416670416457 / 50000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (228314148111 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_37 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (2587473920473 / 3125000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283145448011 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨37, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (2587473920473 / 3125000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283145448011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_38 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82765013915963 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283149425959 / 100000000000000 : ℝ))
      (E := (cell12453 ⟨38, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82765013915963 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (2283149425959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12453_39 : CellCertificate 12453 (893722352023779 / 10000000000000000 : ℝ) (843353636972679 / 500000000000000000 : ℝ) (17043591764863 / 500000000000000 : ℝ)
    (cell12453 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · norm_num [cell12453]
  · have h := gap_lower (n := 12453) (a := (82730886184901 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570788368533 / 25000000000000 : ℝ))
      (E := (cell12453 ⟨39, by decide⟩).energy) (xi := (17043591764863 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12453 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12453]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12453])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12453) (a := (82730886184901 / 100000000000000 : ℝ)) (b := (165446873817 / 100000000000000 : ℝ)) (q := (570788368533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12453])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12453]

theorem cert12454_20 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (83383405201263 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282944164187 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨20, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (83383405201263 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282944164187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_21 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (16669768889871 / 20000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282948170469 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨21, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (16669768889871 / 20000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282948170469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_22 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41657154022669 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141476074913 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨22, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41657154022669 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141476074913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_23 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (5204987247257 / 6250000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (9131824659 / 400000000000 : ℝ))
      (E := (cell12454 ⟨23, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (5204987247257 / 6250000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (9131824659 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_24 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41622654074373 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141480080447 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨24, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41622654074373 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141480080447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_25 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (1040135557381 / 1250000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282964141949 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨25, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (1040135557381 / 1250000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282964141949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_26 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41588202624361 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570742027843 / 25000000000000 : ℝ))
      (E := (cell12454 ⟨26, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41588202624361 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (570742027843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_27 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (10392748761381 / 12500000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282972130801 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨27, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (10392748761381 / 12500000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282972130801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_28 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (83107599085199 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (285372018107 / 12500000000000 : ℝ))
      (E := (cell12454 ⟨28, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (83107599085199 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (285372018107 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_29 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41536616099541 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (228298015629 / 10000000000000 : ℝ))
      (E := (cell12454 ⟨29, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41536616099541 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (228298015629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_30 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (1297482646887 / 1562500000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282984109139 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨30, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (1297482646887 / 1562500000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282984109139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_31 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (83004570658493 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282988122647 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨31, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (83004570658493 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282988122647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_32 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41485137970327 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282992140411 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨32, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41485137970327 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282992140411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_33 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (1295875081497 / 1562500000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282996105707 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨33, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (1295875081497 / 1562500000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2282996105707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_34 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41450879226337 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283000137233 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨34, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41450879226337 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283000137233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_35 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (8286753562013 / 10000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141502059613 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨35, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (8286753562013 / 10000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141502059613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_36 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41416668343607 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141504055697 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨36, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41416668343607 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141504055697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_37 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82799161623117 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283012114667 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨37, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82799161623117 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283012114667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_38 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (82765010397191 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283016129743 / 100000000000000 : ℝ))
      (E := (cell12454 ⟨38, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (82765010397191 / 100000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (2283016129743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12454_39 : CellCertificate 12454 (35747733707261 / 400000000000000 : ℝ) (168657179355353 / 100000000000000000 : ℝ) (170421882306803 / 5000000000000000 : ℝ)
    (cell12454 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · norm_num [cell12454]
  · have h := gap_lower (n := 12454) (a := (41365441489471 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141510049201 / 50000000000000 : ℝ))
      (E := (cell12454 ⟨39, by decide⟩).energy) (xi := (170421882306803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12454 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12454]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12454])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12454) (a := (41365441489471 / 50000000000000 : ℝ)) (b := (661733677 / 400000000000 : ℝ)) (q := (1141510049201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12454])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12454]

theorem cert12455_20 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83383395978603 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282810894497 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨20, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83383395978603 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282810894497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_21 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (20837208886851 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282814866921 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨21, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (20837208886851 / 25000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282814866921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_22 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83314299463647 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282818871447 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨22, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83314299463647 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282818871447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_23 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41639893847117 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (71338214187 / 3125000000000 : ℝ))
      (E := (cell12455 ⟨23, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41639893847117 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (71338214187 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_24 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16649060041247 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282826876809 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨24, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16649060041247 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282826876809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_25 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83210836966891 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282830885313 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨25, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83210836966891 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282830885313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_26 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (8317639794361 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (285354360369 / 12500000000000 : ℝ))
      (E := (cell12455 ⟨26, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (8317639794361 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (285354360369 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_27 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83141983103969 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282838872947 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨27, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83141983103969 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282838872947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_28 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (8310759241571 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456568571657 / 20000000000000 : ℝ))
      (E := (cell12455 ⟨28, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (8310759241571 / 10000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456568571657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_29 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83073225846741 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (57071171043 / 2500000000000 : ℝ))
      (E := (cell12455 ⟨29, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83073225846741 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (57071171043 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_30 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16607776673027 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141425442131 / 50000000000000 : ℝ))
      (E := (cell12455 ⟨30, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16607776673027 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1141425442131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_31 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (83004564939127 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1826283897 / 80000000000 : ℝ))
      (E := (cell12455 ⟨31, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (83004564939127 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (1826283897 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_32 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16594054107423 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282858863209 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨32, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16594054107423 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282858863209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_33 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41468000063829 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282862861973 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨33, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41468000063829 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282862861973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_34 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (3316070147179 / 4000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456573373829 / 20000000000000 : ℝ))
      (E := (cell12455 ⟨34, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (3316070147179 / 4000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456573373829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_35 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (41433765580723 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (285358853437 / 12500000000000 : ℝ))
      (E := (cell12455 ⟨35, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (41433765580723 / 50000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (285358853437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_36 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (82833332542607 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456574971073 / 20000000000000 : ℝ))
      (E := (cell12455 ⟨36, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (82833332542607 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456574971073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_37 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (82799157792153 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282878836443 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨37, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (82799157792153 / 100000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282878836443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_38 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (16553001375887 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456576566007 / 20000000000000 : ℝ))
      (E := (cell12455 ⟨38, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (16553001375887 / 20000000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (456576566007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12455_39 : CellCertificate 12455 (893664337820657 / 10000000000000000 : ℝ) (67457453396967 / 40000000000000000 : ℝ) (21300981165223 / 625000000000000 : ℝ)
    (cell12455 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · norm_num [cell12455]
  · have h := gap_lower (n := 12455) (a := (2068271994349 / 2500000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282886836619 / 100000000000000 : ℝ))
      (E := (cell12455 ⟨39, by decide⟩).energy) (xi := (21300981165223 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12455 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12455]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12455])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12455) (a := (2068271994349 / 2500000000000 : ℝ)) (b := (82709983447 / 50000000000000 : ℝ)) (q := (2282886836619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12455])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12455]

theorem cert12456_20 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (16676677351533 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456535535769 / 20000000000000 : ℝ))
      (E := (cell12456 ⟨20, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (16676677351533 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456535535769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_21 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (16669765329427 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141340837877 / 50000000000000 : ℝ))
      (E := (cell12456 ⟨21, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (16669765329427 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141340837877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_22 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83314290883599 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282685647233 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨22, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83314290883599 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282685647233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_23 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (2081994485849 / 2500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282689655771 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨23, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (2081994485849 / 2500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282689655771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_24 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (10405661533161 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141346823509 / 50000000000000 : ℝ))
      (E := (cell12456 ⟨24, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (10405661533161 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141346823509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_25 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41605414672413 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456539524933 / 20000000000000 : ℝ))
      (E := (cell12456 ⟨25, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41605414672413 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456539524933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_26 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (83176390639983 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282701650561 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨26, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (83176390639983 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282701650561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_27 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (16628395223667 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282705669579 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨27, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (16628395223667 / 20000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282705669579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_28 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (20776896436907 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282709626263 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨28, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (20776896436907 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282709626263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_29 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (10384152436971 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282713640227 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨29, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (10384152436971 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282713640227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_30 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (8303887733083 / 10000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141358827787 / 50000000000000 : ℝ))
      (E := (cell12456 ⟨30, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (8303887733083 / 10000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141358827787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_31 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (1660091184421 / 2000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141360808041 / 50000000000000 : ℝ))
      (E := (cell12456 ⟨31, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (1660091184421 / 2000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (1141360808041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_32 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41485132567413 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570681410203 / 25000000000000 : ℝ))
      (E := (cell12456 ⟨32, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41485132567413 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570681410203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_33 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41467997520359 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282729614549 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨33, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41467997520359 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282729614549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_34 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (10362718613431 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282733655989 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨34, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (10362718613431 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282733655989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_35 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82867526703893 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282737649369 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨35, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82867526703893 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282737649369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_36 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (41416664199547 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456548330879 / 20000000000000 : ℝ))
      (E := (cell12456 ⟨36, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (41416664199547 / 50000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (456548330879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_37 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (20699788490561 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282745613341 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨37, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (20699788490561 / 25000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282745613341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_38 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (10345625420337 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570687411047 / 25000000000000 : ℝ))
      (E := (cell12456 ⟨38, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (10345625420337 / 12500000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (570687411047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12456_39 : CellCertificate 12456 (111704417180011 / 1250000000000000 : ℝ) (1686300898052049 / 1000000000000000000 : ℝ) (13631505495433 / 400000000000000 : ℝ)
    (cell12456 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · norm_num [cell12456]
  · have h := gap_lower (n := 12456) (a := (82730876569957 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282753630083 / 100000000000000 : ℝ))
      (E := (cell12456 ⟨39, by decide⟩).energy) (xi := (13631505495433 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12456 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12456]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12456])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12456) (a := (82730876569957 / 100000000000000 : ℝ)) (b := (41351629187 / 25000000000000 : ℝ)) (q := (2282753630083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12456])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12456]

theorem cert12457_20 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83383377538449 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282544517233 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨20, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83383377538449 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282544517233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_21 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (20837204437137 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456509696083 / 20000000000000 : ℝ))
      (E := (cell12457 ⟨21, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (20837204437137 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456509696083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_22 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41657141152597 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282552477189 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨22, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41657141152597 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282552477189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_23 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83279771175289 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282556511791 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨23, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83279771175289 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282556511791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_24 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (16649056865181 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (91302418861 / 4000000000000 : ℝ))
      (E := (cell12457 ⟨24, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (16649056865181 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (91302418861 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_25 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (16642164344857 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282564476749 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨25, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (16642164344857 / 20000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282564476749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_26 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (1039704791723 / 1250000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456513694519 / 20000000000000 : ℝ))
      (E := (cell12457 ⟨26, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (1039704791723 / 1250000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456513694519 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_27 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83141969134147 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141286231141 / 50000000000000 : ℝ))
      (E := (cell12457 ⟨27, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83141969134147 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141286231141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_28 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83107579080951 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456515289759 / 20000000000000 : ℝ))
      (E := (cell12457 ⟨28, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83107579080951 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456515289759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_29 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (83073213146161 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (285322561669 / 12500000000000 : ℝ))
      (E := (cell12457 ⟨29, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (83073213146161 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (285322561669 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_30 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (20759717824463 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282584481567 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨30, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (20759717824463 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282584481567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_31 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (4150227675213 / 5000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282588474171 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨31, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (4150227675213 / 5000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282588474171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_32 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41485129866893 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282592473223 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨32, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41485129866893 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282592473223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_33 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82935989954989 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456519296111 / 20000000000000 : ℝ))
      (E := (cell12457 ⟨33, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82935989954989 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (456519296111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_34 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82901744136591 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141300219593 / 50000000000000 : ℝ))
      (E := (cell12457 ⟨34, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82901744136591 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (1141300219593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_35 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41433761123737 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282604467633 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨35, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41433761123737 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282604467633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_36 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (41416662128337 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282608449857 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨36, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (41416662128337 / 50000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282608449857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_37 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (82799150133389 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570653111341 / 25000000000000 : ℝ))
      (E := (cell12457 ⟨37, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (82799150133389 / 100000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (570653111341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_38 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (20691249961743 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282616454853 / 100000000000000 : ℝ))
      (E := (cell12457 ⟨38, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (20691249961743 / 25000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (2282616454853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12457_39 : CellCertificate 12457 (89360634153873 / 1000000000000000 : ℝ) (1686165482931911 / 1000000000000000000 : ℝ) (340759580839061 / 10000000000000000 : ℝ)
    (cell12457 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · norm_num [cell12457]
  · have h := gap_lower (n := 12457) (a := (8273087336693 / 10000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (5706551197 / 250000000000 : ℝ))
      (E := (cell12457 ⟨39, by decide⟩).energy) (xi := (340759580839061 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12457 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12457]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12457])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12457) (a := (8273087336693 / 10000000000000 : ℝ)) (b := (16539306881 / 10000000000000 : ℝ)) (q := (5706551197 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12457])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12457]

theorem cert12458_20 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41691684160477 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (142650709463 / 6250000000000 : ℝ))
      (E := (cell12458 ⟨20, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41691684160477 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (142650709463 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_21 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83348808851643 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (142650962341 / 6250000000000 : ℝ))
      (E := (cell12458 ⟨21, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83348808851643 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (142650962341 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_22 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (8331427372843 / 10000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282419361313 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨22, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (8331427372843 / 10000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282419361313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_23 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (4163988145911 / 5000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (57060584093 / 2500000000000 : ℝ))
      (E := (cell12458 ⟨23, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (4163988145911 / 5000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (57060584093 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_24 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (16649055277617 / 20000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282427350327 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨24, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (16649055277617 / 20000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282427350327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_25 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (20802703526317 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282431383193 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨25, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (20802703526317 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282431383193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_26 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83176376037181 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282435349053 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨26, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83176376037181 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282435349053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_27 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (20785490537851 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282439367891 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨27, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (20785490537851 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282439367891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_28 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (259711163799 / 312500000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (891579447 / 39062500000 : ℝ))
      (E := (cell12458 ⟨28, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (259711163799 / 312500000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (891579447 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_29 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83073206797921 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282447342627 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨29, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83073206797921 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282447342627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_30 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83038865266201 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282451362239 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨30, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83038865266201 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282451362239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_31 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (83004547788759 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282455328489 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨31, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (83004547788759 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282455328489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_32 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41485127166997 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (57061484011 / 2500000000000 : ℝ))
      (E := (cell12458 ⟨32, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41485127166997 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (57061484011 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_33 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82935984870469 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (285307917859 / 12500000000000 : ℝ))
      (E := (cell12458 ⟨33, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82935984870469 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (285307917859 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_34 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41450869683453 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141233667949 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨34, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41450869683453 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141233667949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_35 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (41433758896093 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141235670447 / 50000000000000 : ℝ))
      (E := (cell12458 ⟨35, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (41433758896093 / 50000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (1141235670447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_36 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (20708330028837 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (71327354969 / 3125000000000 : ℝ))
      (E := (cell12458 ⟨36, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (20708330028837 / 25000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (71327354969 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_37 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82799146305589 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282479332511 / 100000000000000 : ℝ))
      (E := (cell12458 ⟨37, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82799146305589 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (2282479332511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_38 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (10345624541533 / 12500000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (17831900943 / 781250000000 : ℝ))
      (E := (cell12458 ⟨38, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (10345624541533 / 12500000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (17831900943 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12458_39 : CellCertificate 12458 (111697168764437 / 1250000000000000 : ℝ) (1686030089558521 / 1000000000000000000 : ℝ) (85182882250489 / 2500000000000000 : ℝ)
    (cell12458 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · norm_num [cell12458]
  · have h := gap_lower (n := 12458) (a := (82730870164881 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456497464813 / 20000000000000 : ℝ))
      (E := (cell12458 ⟨39, by decide⟩).energy) (xi := (85182882250489 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12458 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12458]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12458])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12458) (a := (82730870164881 / 100000000000000 : ℝ)) (b := (82689811541 / 50000000000000 : ℝ)) (q := (456497464813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12458])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12458]

theorem cert12459_20 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (4169167955259 / 5000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (57056957447 / 2500000000000 : ℝ))
      (E := (cell12459 ⟨20, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (4169167955259 / 5000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (57056957447 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_21 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83348799956419 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285285288791 / 12500000000000 : ℝ))
      (E := (cell12459 ⟨21, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83348799956419 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285285288791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_22 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83314265153309 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285285787451 / 12500000000000 : ℝ))
      (E := (cell12459 ⟨22, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83314265153309 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285285787451 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_23 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83279754662753 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282290328209 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨23, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83279754662753 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282290328209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_24 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (83245268451827 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282294283429 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨24, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (83245268451827 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282294283429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_25 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41605403243887 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (228229828563 / 10000000000000 : ℝ))
      (E := (cell12459 ⟨25, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41605403243887 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (228229828563 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_26 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41588184369003 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282302279939 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨26, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41588184369003 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282302279939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_27 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (10392744396263 / 12500000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285288290999 / 12500000000000 : ℝ))
      (E := (cell12459 ⟨27, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (10392744396263 / 12500000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (285288290999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_28 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41553782875907 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141155157979 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨28, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41553782875907 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141155157979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_29 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41536600225523 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141157152493 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨29, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41536600225523 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141157152493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_30 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (20759714808969 / 25000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141159148797 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨30, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (20759714808969 / 25000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141159148797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_31 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (5187783879659 / 6250000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570580574017 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨31, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (5187783879659 / 6250000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570580574017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_32 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82970248935451 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282326302467 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨32, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82970248935451 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282326302467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_33 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82935979787159 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282330318621 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨33, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82935979787159 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282330318621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_34 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82901734598391 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282334287547 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨34, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82901734598391 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282334287547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_35 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (82867513338029 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570584567289 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨35, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (82867513338029 / 100000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570584567289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_36 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (41416657987557 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141171132297 / 50000000000000 : ℝ))
      (E := (cell12459 ⟨36, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (41416657987557 / 50000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (1141171132297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_37 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (20699785619711 / 25000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282346274783 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨37, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (20699785619711 / 25000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282346274783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_38 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (20691248204643 / 25000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282350300421 / 100000000000000 : ℝ))
      (E := (cell12459 ⟨38, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (20691248204643 / 25000000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (2282350300421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12459_39 : CellCertificate 12459 (893548363169299 / 10000000000000000 : ℝ) (842947358963321 / 500000000000000000 : ℝ) (170351740936597 / 5000000000000000 : ℝ)
    (cell12459 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · norm_num [cell12459]
  · have h := gap_lower (n := 12459) (a := (2585339592619 / 3125000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570588570821 / 25000000000000 : ℝ))
      (E := (cell12459 ⟨39, by decide⟩).energy) (xi := (170351740936597 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12459 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12459]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12459])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12459) (a := (2585339592619 / 3125000000000 : ℝ)) (b := (165366179561 / 100000000000000 : ℝ)) (q := (570588570821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12459])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12459]

theorem cert12460_20 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83383349891127 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456429059679 / 20000000000000 : ℝ))
      (E := (cell12460 ⟨20, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83383349891127 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456429059679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_21 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (20837197765719 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141074638653 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨21, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (20837197765719 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141074638653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_22 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (20828564144957 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (91286131683 / 4000000000000 : ℝ))
      (E := (cell12460 ⟨22, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (20828564144957 / 25000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (91286131683 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_23 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (10409968301111 / 12500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282157288609 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨23, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (10409968301111 / 12500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282157288609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_24 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83245260517131 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282161270831 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨24, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83245260517131 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282161270831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_25 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41605399435901 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141082650401 / 50000000000000 : ℝ))
      (E := (cell12460 ⟨25, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41605399435901 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (1141082650401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_26 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41588180720157 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570542316313 / 25000000000000 : ℝ))
      (E := (cell12460 ⟨26, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41588180720157 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570542316313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_27 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (83141948190249 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456434656833 / 20000000000000 : ℝ))
      (E := (cell12460 ⟨27, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (83141948190249 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456434656833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_28 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (10388444886169 / 12500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282177302153 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨28, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (10388444886169 / 12500000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282177302153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_29 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (1298018657899 / 1562500000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (4564362527 / 200000000000 : ℝ))
      (E := (cell12460 ⟨29, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (1298018657899 / 1562500000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (4564362527 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_30 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41519426603439 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282185287631 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨30, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41519426603439 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282185287631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_31 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41502268180809 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282189259879 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨31, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41502268180809 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282189259879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_32 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82970243538157 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282193299303 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨32, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82970243538157 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282193299303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_33 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41467987352529 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570549322671 / 25000000000000 : ℝ))
      (E := (cell12460 ⟨33, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41467987352529 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570549322671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_34 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82901729831047 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570550323533 / 25000000000000 : ℝ))
      (E := (cell12460 ⟨34, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82901729831047 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570550323533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_35 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (16573501777001 / 20000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (35659457069 / 1562500000000 : ℝ))
      (E := (cell12460 ⟨35, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (16573501777001 / 20000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (35659457069 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_36 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82833311835973 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (71319040121 / 3125000000000 : ℝ))
      (E := (cell12460 ⟨36, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82833311835973 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (71319040121 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_37 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (82799138653151 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282213272183 / 100000000000000 : ℝ))
      (E := (cell12460 ⟨37, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (82799138653151 / 100000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (2282213272183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_38 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (41382494652947 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570554319163 / 25000000000000 : ℝ))
      (E := (cell12460 ⟨38, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (41382494652947 / 50000000000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (570554319163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12460_39 : CellCertificate 12460 (223379845174763 / 2500000000000000 : ℝ) (421439842007759 / 250000000000000000 : ℝ) (170337719725729 / 5000000000000000 : ℝ)
    (cell12460 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · norm_num [cell12460]
  · have h := gap_lower (n := 12460) (a := (323167436577 / 390625000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456444259551 / 20000000000000 : ℝ))
      (E := (cell12460 ⟨39, by decide⟩).energy) (xi := (170337719725729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12460 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12460]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12460])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12460) (a := (323167436577 / 390625000000 : ℝ)) (b := (20669092281 / 12500000000000 : ℝ)) (q := (456444259551 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12460])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12460]

theorem cert12461_20 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83383340678793 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570503088239 / 25000000000000 : ℝ))
      (E := (cell12461 ⟨20, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83383340678793 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570503088239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_21 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83348782171013 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282016356673 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨21, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83348782171013 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282016356673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_22 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (20828562001997 / 25000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570505084679 / 25000000000000 : ℝ))
      (E := (cell12461 ⟨22, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (20828562001997 / 25000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570505084679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_23 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (5204983634789 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282024361571 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨23, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (5204983634789 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282024361571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_24 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83245252583997 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282028370883 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨24, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83245252583997 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282028370883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_25 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83210791257353 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282032370339 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨25, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83210791257353 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282032370339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_26 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41588177072053 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (228203636339 / 10000000000000 : ℝ))
      (E := (cell12461 ⟨26, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41588177072053 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (228203636339 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_27 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (83141941211837 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282040353251 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨27, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (83141941211837 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282040353251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_28 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (16621510485659 / 20000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285255542863 / 12500000000000 : ℝ))
      (E := (cell12461 ⟨28, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (16621510485659 / 20000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285255542863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_29 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (5192074235087 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282048335099 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨29, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (5192074235087 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282048335099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_30 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41519423589603 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (35657067693 / 1562500000000 : ℝ))
      (E := (cell12461 ⟨30, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41519423589603 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (35657067693 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_31 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41502265324989 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282056336951 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨31, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41502265324989 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282056336951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_32 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (8297023814211 / 10000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285257543869 / 12500000000000 : ℝ))
      (E := (cell12461 ⟨32, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (8297023814211 / 10000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (285257543869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_33 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (41467984812083 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282064317623 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨33, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (41467984812083 / 50000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282064317623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_34 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (10362715633109 / 12500000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282068355657 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨34, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (10362715633109 / 12500000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282068355657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_35 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82867504433111 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141036174643 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨35, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82867504433111 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141036174643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_36 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (20708326924481 / 25000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141038149793 / 50000000000000 : ℝ))
      (E := (cell12461 ⟨36, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (20708326924481 / 25000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (1141038149793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_37 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82799134828513 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (228208032471 / 10000000000000 : ℝ))
      (E := (cell12461 ⟨37, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82799134828513 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (228208032471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_38 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (82764985794231 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570521077019 / 25000000000000 : ℝ))
      (E := (cell12461 ⟨38, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (82764985794231 / 100000000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (570521077019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12461_39 : CellCertificate 12461 (89349040270367 / 1000000000000000 : ℝ) (168562403986647 / 100000000000000000 : ℝ) (340647401735433 / 10000000000000000 : ℝ)
    (cell12461 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · norm_num [cell12461]
  · have h := gap_lower (n := 12461) (a := (5170678785287 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282088308781 / 100000000000000 : ℝ))
      (E := (cell12461 ⟨39, by decide⟩).energy) (xi := (340647401735433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12461 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12461]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12461])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12461) (a := (5170678785287 / 6250000000000 : ℝ)) (b := (165339299141 / 100000000000000 : ℝ)) (q := (2282088308781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12461])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12461]

theorem cert12462_20 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (4169166573409 / 5000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140939730781 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨20, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (4169166573409 / 5000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140939730781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_21 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (8334877328083 / 10000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (35654428623 / 1562500000000 : ℝ))
      (E := (cell12462 ⟨21, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (8334877328083 / 10000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (35654428623 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_22 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83314239437789 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281887439531 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨22, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83314239437789 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281887439531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_23 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83279729905961 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281891430447 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨23, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83279729905961 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281891430447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_24 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (10405655581553 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (228189546689 / 10000000000000 : ℝ))
      (E := (cell12462 ⟨24, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (10405655581553 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (228189546689 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_25 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (3328431345777 / 4000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (71309357371 / 3125000000000 : ℝ))
      (E := (cell12462 ⟨25, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (3328431345777 / 4000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (71309357371 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_26 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83176346849379 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281903457563 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨26, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83176346849379 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281903457563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_27 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (20785483558717 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570476854603 / 25000000000000 : ℝ))
      (E := (cell12462 ⟨27, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (20785483558717 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570476854603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_28 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83107545768641 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281911438213 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨28, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83107545768641 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281911438213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_29 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (20768295354653 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (57047886533 / 2500000000000 : ℝ))
      (E := (cell12462 ⟨29, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (20768295354653 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (57047886533 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_30 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (83038841152859 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281919431759 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨30, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (83038841152859 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281919431759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_31 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (10375565617453 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (114096170513 / 5000000000000 : ℝ))
      (E := (cell12462 ⟨31, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (10375565617453 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (114096170513 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_32 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (8297023274731 / 10000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281927457413 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨32, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (8297023274731 / 10000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281927457413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_33 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82935964544483 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570482849859 / 25000000000000 : ℝ))
      (E := (cell12462 ⟨33, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82935964544483 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (570482849859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_34 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82901720299867 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140967706769 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨34, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82901720299867 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140967706769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_35 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (20716874995587 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (285242430319 / 12500000000000 : ℝ))
      (E := (cell12462 ⟨35, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (20716874995587 / 25000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (285242430319 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_36 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (10354162945121 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140971714497 / 50000000000000 : ℝ))
      (E := (cell12462 ⟨36, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (10354162945121 / 12500000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (1140971714497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_37 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82799131004927 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (142621714523 / 6250000000000 : ℝ))
      (E := (cell12462 ⟨37, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82799131004927 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (142621714523 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_38 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (82764982283583 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (228195139469 / 10000000000000 : ℝ))
      (E := (cell12462 ⟨38, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (82764982283583 / 100000000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (228195139469 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12462_39 : CellCertificate 12462 (893461429182067 / 10000000000000000 : ℝ) (1685488733427709 / 1000000000000000000 : ℝ) (85154842180951 / 2500000000000000 : ℝ)
    (cell12462 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · norm_num [cell12462]
  · have h := gap_lower (n := 12462) (a := (5170678585403 / 6250000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281955433763 / 100000000000000 : ℝ))
      (E := (cell12462 ⟨39, by decide⟩).energy) (xi := (85154842180951 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12462 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12462]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12462])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12462) (a := (5170678585403 / 6250000000000 : ℝ)) (b := (165325862241 / 100000000000000 : ℝ)) (q := (2281955433763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12462])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12462]

theorem cert12463_20 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (16676664451857 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285218328027 / 12500000000000 : ℝ))
      (E := (cell12463 ⟨20, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (16676664451857 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (285218328027 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_21 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83348764392327 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (114087530973 / 5000000000000 : ℝ))
      (E := (cell12463 ⟨21, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83348764392327 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (114087530973 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_22 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83314230869229 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140877297261 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨22, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83314230869229 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140877297261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_23 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41639860828449 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281758611887 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨23, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41639860828449 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281758611887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_24 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (20811309180603 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (5704406543 / 250000000000 : ℝ))
      (E := (cell12463 ⟨24, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (20811309180603 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (5704406543 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_25 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83210776033019 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281766614143 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨25, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83210776033019 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281766614143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_26 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (16635267911227 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281770606167 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨26, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (16635267911227 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281770606167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_27 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41570963629671 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281774596487 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨27, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41570963629671 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281774596487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_28 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83107539110391 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281778588081 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨28, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83107539110391 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281778588081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_29 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (83073175077197 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281782583697 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨29, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (83073175077197 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281782583697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_30 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41519417563919 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (570446646463 / 25000000000000 : ℝ))
      (E := (cell12463 ⟨30, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41519417563919 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (570446646463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_31 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (20751129807639 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281790596831 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨31, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (20751129807639 / 25000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281790596831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_32 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41485113676879 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (45635891203 / 2000000000000 : ℝ))
      (E := (cell12463 ⟨32, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41485113676879 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (45635891203 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_33 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82935959466007 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281798594687 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨33, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82935959466007 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281798594687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_34 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82901715536031 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140901292471 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨34, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82901715536031 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140901292471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_35 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (16573499106543 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281806590821 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨35, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (16573499106543 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281806590821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_36 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (41416649712551 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281810554841 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨36, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (41416649712551 / 50000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281810554841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_37 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (16559825436479 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140907297577 / 50000000000000 : ℝ))
      (E := (cell12463 ⟨37, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (16559825436479 / 20000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (1140907297577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_38 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82764978773949 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (91272743807 / 4000000000000 : ℝ))
      (E := (cell12463 ⟨38, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82764978773949 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (91272743807 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12463_39 : CellCertificate 12463 (446716230066579 / 5000000000000000 : ℝ) (842676724354761 / 500000000000000000 : ℝ) (68118268083051 / 2000000000000000 : ℝ)
    (cell12463 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · norm_num [cell12463]
  · have h := gap_lower (n := 12463) (a := (82730854169279 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281822555301 / 100000000000000 : ℝ))
      (E := (cell12463 ⟨39, by decide⟩).energy) (xi := (68118268083051 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12463 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12463]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12463])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12463) (a := (82730854169279 / 100000000000000 : ℝ)) (b := (165312427547 / 100000000000000 : ℝ)) (q := (2281822555301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12463])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12463]

theorem cert12464_20 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83383313052109 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456322756533 / 20000000000000 : ℝ))
      (E := (cell12464 ⟨20, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83383313052109 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456322756533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_21 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83348755505503 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281617802883 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨21, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83348755505503 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281617802883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_22 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83314222302309 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (228162180369 / 10000000000000 : ℝ))
      (E := (cell12464 ⟨22, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83314222302309 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (228162180369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_23 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16655942681887 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570406447311 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨23, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16655942681887 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570406447311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_24 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (2081130719849 / 2500000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456325964363 / 20000000000000 : ℝ))
      (E := (cell12464 ⟨24, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (2081130719849 / 2500000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456325964363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_25 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41605384211567 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570408447103 / 25000000000000 : ℝ))
      (E := (cell12464 ⟨25, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41605384211567 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (570408447103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_26 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (20794083066093 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456327561841 / 20000000000000 : ℝ))
      (E := (cell12464 ⟨26, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (20794083066093 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (456327561841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_27 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83141920285259 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281641770639 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨27, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83141920285259 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281641770639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_28 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16621506490709 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281645792509 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨28, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16621506490709 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281645792509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_29 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (16614633747429 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140824909583 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨29, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (16614633747429 / 20000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140824909583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_30 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (83038829104141 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140826897317 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨30, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (83038829104141 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140826897317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_31 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (3320180540911 / 4000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (57041444491 / 2500000000000 : ℝ))
      (E := (cell12464 ⟨31, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (3320180540911 / 4000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (57041444491 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_32 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (20742555490363 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281661776239 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨32, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (20742555490363 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281661776239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_33 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82935954388739 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281665786257 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨33, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82935954388739 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281665786257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_34 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (20725427693341 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281669811287 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨34, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (20725427693341 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281669811287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_35 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (20716872771053 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (142604612131 / 6250000000000 : ℝ))
      (E := (cell12464 ⟨35, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (20716872771053 / 25000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (142604612131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_36 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (10354161911291 / 12500000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140838897193 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨36, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (10354161911291 / 12500000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140838897193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_37 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41399561680457 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281681754421 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨37, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41399561680457 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281681754421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_38 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (82764975265329 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140842896089 / 50000000000000 : ℝ))
      (E := (cell12464 ⟨38, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (82764975265329 / 100000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (1140842896089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12464_39 : CellCertificate 12464 (893403495555857 / 10000000000000000 : ℝ) (42130454642667 / 25000000000000000 : ℝ) (170281658404237 / 5000000000000000 : ℝ)
    (cell12464 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · norm_num [cell12464]
  · have h := gap_lower (n := 12464) (a := (41365425486543 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281689790797 / 100000000000000 : ℝ))
      (E := (cell12464 ⟨39, by decide⟩).energy) (xi := (170281658404237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12464 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12464]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12464])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12464) (a := (41365425486543 / 50000000000000 : ℝ)) (b := (82649497529 / 50000000000000 : ℝ)) (q := (2281689790797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12464])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12464]

theorem cert12465_20 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20845825961663 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281481053417 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨20, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20845825961663 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281481053417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_21 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83348746620357 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281485040421 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨21, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83348746620357 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281485040421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_22 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20828553434257 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570372266759 / 25000000000000 : ℝ))
      (E := (cell12465 ⟨22, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20828553434257 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570372266759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_23 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83279705163571 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281493079169 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨23, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83279705163571 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281493079169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_24 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83245220867069 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (71296783773 / 3125000000000 : ℝ))
      (E := (cell12465 ⟨24, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83245220867069 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (71296783773 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_25 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83210760814769 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (71296908607 / 3125000000000 : ℝ))
      (E := (cell12465 ⟨25, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83210760814769 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (71296908607 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_26 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (8317632497409 / 10000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281505066677 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨26, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (8317632497409 / 10000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281505066677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_27 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83141913312617 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281509057709 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨27, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83141913312617 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281509057709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_28 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83107525798101 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281513051499 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨28, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83107525798101 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281513051499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_29 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (41536581199229 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (285189631349 / 12500000000000 : ℝ))
      (E := (cell12465 ⟨29, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (41536581199229 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (285189631349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_30 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (83038823081769 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281521058103 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨30, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (83038823081769 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281521058103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_31 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (41502253908139 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281525017203 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨31, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (41502253908139 / 50000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281525017203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_32 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82970216570393 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (285191130893 / 12500000000000 : ℝ))
      (E := (cell12465 ⟨32, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82970216570393 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (285191130893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_33 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82935949312679 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456306606541 / 20000000000000 : ℝ))
      (E := (cell12465 ⟨33, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82935949312679 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (456306606541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_34 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (16580341202373 / 20000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281537033993 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨34, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (16580341202373 / 20000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281537033993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_35 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82867486636839 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281541052377 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨35, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82867486636839 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281541052377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_36 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (16566658231329 / 20000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (228154503037 / 10000000000000 : ℝ))
      (E := (cell12465 ⟨36, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (16566658231329 / 20000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (228154503037 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_37 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82799119540487 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281549027471 / 100000000000000 : ℝ))
      (E := (cell12465 ⟨37, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82799119540487 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (2281549027471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_38 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (82764971757723 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (285194130547 / 12500000000000 : ℝ))
      (E := (cell12465 ⟨38, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (82764971757723 / 100000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (285194130547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12465_39 : CellCertificate 12465 (893374535449079 / 10000000000000000 : ℝ) (842541472206977 / 500000000000000000 : ℝ) (340535297902147 / 10000000000000000 : ℝ)
    (cell12465 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · norm_num [cell12465]
  · have h := gap_lower (n := 12465) (a := (20682711944467 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570389255713 / 25000000000000 : ℝ))
      (E := (cell12465 ⟨39, by decide⟩).energy) (xi := (340535297902147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12465 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12465]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12465])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12465) (a := (20682711944467 / 25000000000000 : ℝ)) (b := (82642782387 / 50000000000000 : ℝ)) (q := (570389255713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12465])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12465]

theorem cert12466_20 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (2605727957591 / 3125000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281348378223 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨20, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (2605727957591 / 3125000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281348378223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_21 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (8334873773689 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (142584524397 / 6250000000000 : ℝ))
      (E := (cell12466 ⟨21, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (8334873773689 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (142584524397 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_22 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (16662841034677 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281356384563 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨22, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (16662841034677 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281356384563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_23 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83279696919307 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570340091253 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨23, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83279696919307 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570340091253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_24 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83245212941737 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281364393967 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨24, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83245212941737 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281364393967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_25 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (3328430128317 / 4000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570342089609 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨25, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (3328430128317 / 4000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570342089609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_26 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (8317631768529 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (456274475717 / 20000000000000 : ℝ))
      (E := (cell12466 ⟨26, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (8317631768529 / 10000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (456274475717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_27 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83141906341417 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (114068817043 / 5000000000000 : ℝ))
      (E := (cell12466 ⟨27, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83141906341417 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (114068817043 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_28 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83107519144059 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281380365053 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨28, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83107519144059 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281380365053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_29 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83073156061133 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (285173042131 / 12500000000000 : ℝ))
      (E := (cell12466 ⟨29, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83073156061133 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (285173042131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_30 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83038817060721 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (456277675253 / 20000000000000 : ℝ))
      (E := (cell12466 ⟨30, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83038817060721 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (456277675253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_31 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (83004502111067 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (71293511501 / 3125000000000 : ℝ))
      (E := (cell12466 ⟨31, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (83004502111067 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (71293511501 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_32 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82970211180579 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570349093217 / 25000000000000 : ℝ))
      (E := (cell12466 ⟨32, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82970211180579 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (570349093217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_33 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (41467972118913 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (456280066807 / 20000000000000 : ℝ))
      (E := (cell12466 ⟨33, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (41467972118913 / 50000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (456280066807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_34 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (16580340250307 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281404370227 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨34, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (16580340250307 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281404370227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_35 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (16573496438119 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281408365667 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨35, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (16573496438119 / 20000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281408365667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_36 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82833287024053 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (91256492857 / 4000000000000 : ℝ))
      (E := (cell12466 ⟨36, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82833287024053 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (91256492857 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_37 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82799115721111 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140708177829 / 50000000000000 : ℝ))
      (E := (cell12466 ⟨37, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82799115721111 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (1140708177829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_38 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (82764968251129 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281420351773 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨38, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (82764968251129 / 100000000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281420351773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12466_39 : CellCertificate 12466 (446672789905871 / 5000000000000000 : ℝ) (1684947724826119 / 1000000000000000000 : ℝ) (340507283694961 / 10000000000000000 : ℝ)
    (cell12466 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · norm_num [cell12466]
  · have h := gap_lower (n := 12466) (a := (10341355572953 / 12500000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281424368869 / 100000000000000 : ℝ))
      (E := (cell12466 ⟨39, by decide⟩).energy) (xi := (340507283694961 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12466 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12466]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12466])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12466) (a := (10341355572953 / 12500000000000 : ℝ)) (b := (165272136693 / 100000000000000 : ℝ)) (q := (2281424368869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12466])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12466]

theorem cert12467_20 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (8338328544089 / 10000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (57030393927 / 2500000000000 : ℝ))
      (E := (cell12467 ⟨20, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (8338328544089 / 10000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (57030393927 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_21 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83348728855101 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140609868061 / 50000000000000 : ℝ))
      (E := (cell12467 ⟨21, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83348728855101 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140609868061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_22 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83314196611381 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281223756271 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨22, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83314196611381 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281223756271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_23 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41639844338321 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (22812277051 / 1000000000000 : ℝ))
      (E := (cell12467 ⟨23, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41639844338321 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (22812277051 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_24 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (16649041003593 / 20000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570307925789 / 25000000000000 : ℝ))
      (E := (cell12467 ⟨24, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (16649041003593 / 20000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570307925789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_25 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83210745602601 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281235754191 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨25, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83210745602601 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281235754191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_26 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (8317631039797 / 10000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (228123974493 / 10000000000000 : ℝ))
      (E := (cell12467 ⟨26, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (8317631039797 / 10000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (228123974493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_27 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41570949685829 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281243736931 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨27, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41570949685829 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281243736931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_28 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83107512491419 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570311933293 / 25000000000000 : ℝ))
      (E := (cell12467 ⟨28, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83107512491419 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570311933293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_29 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (83073149725171 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570312934099 / 25000000000000 : ℝ))
      (E := (cell12467 ⟨29, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (83073149725171 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570312934099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_30 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (20759702760249 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570313922657 / 25000000000000 : ℝ))
      (E := (cell12467 ⟨30, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (20759702760249 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (570313922657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_31 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (4150224820357 / 5000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (71289366097 / 3125000000000 : ℝ))
      (E := (cell12467 ⟨31, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (4150224820357 / 5000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (71289366097 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_32 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (20742551448003 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281263694873 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨32, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (20742551448003 / 25000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281263694873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_33 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82935939164179 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (285158461281 / 12500000000000 : ℝ))
      (E := (cell12467 ⟨33, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82935939164179 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (285158461281 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_34 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82901696492373 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140635851411 / 50000000000000 : ℝ))
      (E := (cell12467 ⟨34, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82901696492373 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (1140635851411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_35 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82867477745481 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281275733963 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨35, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82867477745481 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281275733963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_36 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82833282892551 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281279726183 / 100000000000000 : ℝ))
      (E := (cell12467 ⟨36, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82833282892551 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (2281279726183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_37 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (41399555951393 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (114064186949 / 5000000000000 : ℝ))
      (E := (cell12467 ⟨37, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (41399555951393 / 50000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (114064186949 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_38 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (82764964745549 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (35645120537 / 1562500000000 : ℝ))
      (E := (cell12467 ⟨38, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (82764964745549 / 100000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (35645120537 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12467_39 : CellCertificate 12467 (22332915716069 / 250000000000000 : ℝ) (1684812526937949 / 1000000000000000000 : ℝ) (85119818546401 / 2500000000000000 : ℝ)
    (cell12467 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · norm_num [cell12467]
  · have h := gap_lower (n := 12467) (a := (16546168278071 / 20000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456258342289 / 20000000000000 : ℝ))
      (E := (cell12467 ⟨39, by decide⟩).energy) (xi := (85119818546401 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12467 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12467]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12467])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12467) (a := (16546168278071 / 20000000000000 : ℝ)) (b := (5164334713 / 3125000000000 : ℝ)) (q := (456258342289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12467])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12467]

theorem cert12468_20 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (16676655248117 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281083131737 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨20, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (16676655248117 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281083131737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_21 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (20837179993747 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570271784003 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨21, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (20837179993747 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570271784003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_22 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41657094025507 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281091123859 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨22, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41657094025507 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281091123859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_23 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41639840217787 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281095157761 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨23, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41639840217787 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281095157761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_24 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83245197095751 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140549562503 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨24, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83245197095751 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140549562503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_25 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (20802684499699 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (45622062919 / 2000000000000 : ℝ))
      (E := (cell12468 ⟨25, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (20802684499699 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (45622062919 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_26 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (8317630311213 / 10000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (142569197857 / 6250000000000 : ℝ))
      (E := (cell12468 ⟨26, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (8317630311213 / 10000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (142569197857 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_27 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (4157094620167 / 5000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570277782271 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨27, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (4157094620167 / 5000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570277782271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_28 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (83107505840181 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456223031171 / 20000000000000 : ℝ))
      (E := (cell12468 ⟨28, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (83107505840181 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456223031171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_29 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (20768285847643 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570279782977 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨29, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (20768285847643 / 25000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570279782977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_30 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (16607761004519 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281123118173 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨30, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (16607761004519 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281123118173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_31 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41502245352249 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570281779233 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨31, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41502245352249 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570281779233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_32 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82970200404689 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456226226047 / 20000000000000 : ℝ))
      (E := (cell12468 ⟨32, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82970200404689 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (456226226047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_33 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82935934091739 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281135159903 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨33, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82935934091739 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281135159903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_34 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41450845867189 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281139148947 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨34, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41450845867189 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281139148947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_35 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (16573494660299 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281143157271 / 100000000000000 : ℝ))
      (E := (cell12468 ⟨35, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (16573494660299 / 20000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (2281143157271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_36 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (41416639381069 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (285143390923 / 12500000000000 : ℝ))
      (E := (cell12468 ⟨36, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (41416639381069 / 50000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (285143390923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_37 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82799108085513 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (35642986231 / 1562500000000 : ℝ))
      (E := (cell12468 ⟨37, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82799108085513 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (35642986231 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_38 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (82764961240981 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140577566081 / 50000000000000 : ℝ))
      (E := (cell12468 ⟨38, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (82764961240981 / 100000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (1140577566081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12468_39 : CellCertificate 12468 (17865753638821 / 200000000000000 : ℝ) (842338675372111 / 500000000000000000 : ℝ) (170225634686383 / 5000000000000000 : ℝ)
    (cell12468 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · norm_num [cell12468]
  · have h := gap_lower (n := 12468) (a := (4136541909903 / 5000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570289777321 / 25000000000000 : ℝ))
      (E := (cell12468 ⟨39, by decide⟩).energy) (xi := (170225634686383 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12468 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12468]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12468])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12468) (a := (4136541909903 / 5000000000000 : ℝ)) (b := (82622643571 / 50000000000000 : ℝ)) (q := (570289777321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12468])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12468]

theorem cert12469_20 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (20845816760499 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456190123741 / 20000000000000 : ℝ))
      (E := (cell12469 ⟨20, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (20845816760499 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (456190123741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_21 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83348711096553 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280954648299 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨21, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83348711096553 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280954648299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_22 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (16662835898457 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280958603933 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨22, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (16662835898457 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280958603933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_23 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (16655934439221 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280962606343 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨23, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (16655934439221 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280962606343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_24 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (16649037835019 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280966601167 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨24, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (16649037835019 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280966601167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_25 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (8321073039651 / 10000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (570242648021 / 25000000000000 : ℝ))
      (E := (cell12469 ⟨25, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (8321073039651 / 10000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (570242648021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_26 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (8317629582777 / 10000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140487291269 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨26, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (8317629582777 / 10000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140487291269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_27 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83141885436463 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280978634159 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨27, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83141885436463 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280978634159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_28 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (10388437398793 / 12500000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140491316553 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨28, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (10388437398793 / 12500000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140491316553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_29 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41536568528667 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280986582051 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨29, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41536568528667 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280986582051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_30 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (83038799005517 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280990600413 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨30, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (83038799005517 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280990600413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_31 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (4150224250157 / 5000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280994573517 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨31, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (4150224250157 / 5000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2280994573517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_32 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (20742548754653 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140499310209 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨32, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (20742548754653 / 25000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140499310209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_33 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (16587185804101 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (570250656471 / 25000000000000 : ℝ))
      (E := (cell12469 ⟨33, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (16587185804101 / 20000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (570250656471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_34 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (1658033739551 / 2000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140503295719 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨34, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (1658033739551 / 2000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140503295719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_35 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41433734429319 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140505288491 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨35, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41433734429319 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140505288491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_36 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (5177079664551 / 6250000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140507291829 / 50000000000000 : ℝ))
      (E := (cell12469 ⟨36, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (5177079664551 / 6250000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (1140507291829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_37 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82799104269291 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281018612379 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨37, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82799104269291 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281018612379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_38 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (41382478868713 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281022605157 / 100000000000000 : ℝ))
      (E := (cell12469 ⟨38, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (41382478868713 / 50000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (2281022605157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12469_39 : CellCertificate 12469 (893258739705529 / 10000000000000000 : ℝ) (336908439247943 / 200000000000000000 : ℝ) (68084653851027 / 2000000000000000 : ℝ)
    (cell12469 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · norm_num [cell12469]
  · have h := gap_lower (n := 12469) (a := (82730835006739 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (71282081909 / 3125000000000 : ℝ))
      (E := (cell12469 ⟨39, by decide⟩).energy) (xi := (68084653851027 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12469 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12469]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12469])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12469) (a := (82730835006739 / 100000000000000 : ℝ)) (b := (16523186567 / 10000000000000 : ℝ)) (q := (71282081909 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12469])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12469]

theorem cert12470_20 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83383257845123 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228081815973 / 10000000000000 : ℝ))
      (E := (cell12470 ⟨20, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83383257845123 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228081815973 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_21 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (41674351109897 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570205539107 / 25000000000000 : ℝ))
      (E := (cell12470 ⟨21, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (41674351109897 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570205539107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_22 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83314170935193 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (142551633637 / 6250000000000 : ℝ))
      (E := (cell12470 ⟨22, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83314170935193 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (142551633637 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_23 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83279663958233 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140415054587 / 50000000000000 : ℝ))
      (E := (cell12470 ⟨23, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83279663958233 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (1140415054587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_24 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (41622590627999 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280834131641 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨24, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (41622590627999 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280834131641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_25 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83210722795743 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280838150967 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨25, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83210722795743 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280838150967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_26 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83176288544889 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280842112201 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨26, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83176288544889 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280842112201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_27 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (3325675138841 / 4000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (57021153383 / 2500000000000 : ℝ))
      (E := (cell12470 ⟨27, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (3325675138841 / 4000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (57021153383 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_28 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83107492541909 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280850106481 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨28, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83107492541909 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280850106481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_29 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (83073130725459 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228085414529 / 10000000000000 : ℝ))
      (E := (cell12470 ⟨29, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (83073130725459 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (228085414529 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_30 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (41519396494881 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280858137347 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨30, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (41519396494881 / 50000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280858137347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_31 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (16600895860613 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (18246897147 / 800000000000 : ℝ))
      (E := (cell12470 ⟨31, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (16600895860613 / 20000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (18246897147 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_32 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (4148509481689 / 5000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (456173221377 / 20000000000000 : ℝ))
      (E := (cell12470 ⟨32, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (4148509481689 / 5000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (456173221377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_33 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82935923950477 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280870146749 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨33, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82935923950477 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280870146749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_34 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (8290168222189 / 10000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570218522219 / 25000000000000 : ℝ))
      (E := (cell12470 ⟨34, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (8290168222189 / 10000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (570218522219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_35 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82867464416909 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280878110313 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨35, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82867464416909 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280878110313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_36 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82833270504583 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280882095009 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨36, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82833270504583 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280882095009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_37 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (2069977511353 / 2500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280886102459 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨37, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (2069977511353 / 2500000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280886102459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_38 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82764954234883 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280890133353 / 100000000000000 : ℝ))
      (E := (cell12470 ⟨38, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82764954234883 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (2280890133353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12470_39 : CellCertificate 12470 (446614900967557 / 5000000000000000 : ℝ) (168440706341921 / 100000000000000000 : ℝ) (170197636915701 / 5000000000000000 : ℝ)
    (cell12470 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · norm_num [cell12470]
  · have h := gap_lower (n := 12470) (a := (82730831816391 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (142555883091 / 6250000000000 : ℝ))
      (E := (cell12470 ⟨39, by decide⟩).energy) (xi := (170197636915701 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12470 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12470]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12470])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12470) (a := (82730831816391 / 100000000000000 : ℝ)) (b := (103261529 / 62500000000 : ℝ)) (q := (142555883091 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12470])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12470]

theorem cert12471_20 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41691624324983 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140342848279 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨20, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41691624324983 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140342848279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_21 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83348693344711 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (57017242967 / 2500000000000 : ℝ))
      (E := (cell12471 ⟨21, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83348693344711 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (57017242967 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_22 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83314162379737 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280693726637 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨22, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83314162379737 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280693726637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_23 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41639827860979 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140348862291 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨23, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41639827860979 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140348862291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_24 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41622586669229 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280701716429 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨24, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41622586669229 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280701716429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_25 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41605357598247 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (17818013327 / 781250000000 : ℝ))
      (E := (cell12471 ⟨25, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41605357598247 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (17818013327 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_26 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83176281263487 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140354848153 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨26, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83176281263487 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140354848153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_27 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (20785467876757 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456142738197 / 20000000000000 : ℝ))
      (E := (cell12471 ⟨27, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (20785467876757 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456142738197 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_28 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (83107485894873 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280717692869 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨28, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (83107485894873 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280717692869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_29 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (16614624878989 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280721704697 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨29, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (16614624878989 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280721704697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_30 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (2594962092979 / 3125000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (228072567049 / 10000000000000 : ℝ))
      (E := (cell12471 ⟨30, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (2594962092979 / 3125000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (228072567049 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_31 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (41502236802137 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (57018242737 / 2500000000000 : ℝ))
      (E := (cell12471 ⟨31, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (41502236802137 / 50000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (57018242737 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_32 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82970184250191 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456146741343 / 20000000000000 : ℝ))
      (E := (cell12471 ⟨32, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82970184250191 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (456146741343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_33 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (16587183776331 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280737663941 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨33, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (16587183776331 / 20000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280737663941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_34 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (20725419366849 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280741699849 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨34, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (20725419366849 / 25000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280741699849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_35 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82867459976307 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140372849329 / 50000000000000 : ℝ))
      (E := (cell12471 ⟨35, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82867459976307 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (1140372849329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_36 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82833266377439 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (570187415359 / 25000000000000 : ℝ))
      (E := (cell12471 ⟨36, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82833266377439 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (570187415359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_37 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (82799096639999 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280753706333 / 100000000000000 : ℝ))
      (E := (cell12471 ⟨37, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (82799096639999 / 100000000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (2280753706333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_38 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (10345618841669 / 12500000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (91230306323 / 4000000000000 : ℝ))
      (E := (cell12471 ⟨38, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (10345618841669 / 12500000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (91230306323 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12471_39 : CellCertificate 12471 (893200868628723 / 10000000000000000 : ℝ) (105266997017343 / 62500000000000000 : ℝ) (340367283100257 / 10000000000000000 : ℝ)
    (cell12471 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · norm_num [cell12471]
  · have h := gap_lower (n := 12471) (a := (10341353578377 / 12500000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (228076169309 / 10000000000000 : ℝ))
      (E := (cell12471 ⟨39, by decide⟩).energy) (xi := (340367283100257 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12471 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12471]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12471])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12471) (a := (10341353578377 / 12500000000000 : ℝ)) (b := (165205029331 / 100000000000000 : ℝ)) (q := (228076169309 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12471])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12471]

theorem cert12472_20 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (20845809864131 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280553345701 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨20, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (20845809864131 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280553345701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_21 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (10418585558913 / 12500000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (142534833441 / 6250000000000 : ℝ))
      (E := (cell12472 ⟨21, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (10418585558913 / 12500000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (142534833441 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_22 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83314153825917 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280561310969 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨22, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83314153825917 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280561310969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_23 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83279647487279 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (570141333979 / 25000000000000 : ℝ))
      (E := (cell12472 ⟨23, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83279647487279 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (570141333979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_24 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (20811291355619 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280569355533 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨24, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (20811291355619 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280569355533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_25 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (41605353799381 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140286657563 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨25, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (41605353799381 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140286657563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_26 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83176273983563 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (456115466971 / 20000000000000 : ℝ))
      (E := (cell12472 ⟨26, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83176273983563 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (456115466971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_27 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83141864544469 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (57014532529 / 2500000000000 : ℝ))
      (E := (cell12472 ⟨27, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83141864544469 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (57014532529 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_28 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (41553739624619 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (570146333457 / 25000000000000 : ℝ))
      (E := (cell12472 ⟨28, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (41553739624619 / 50000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (570146333457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_29 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (649008734889 / 781250000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280589318739 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨29, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (649008734889 / 781250000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280589318739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_30 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (83038780962217 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (114029665841 / 5000000000000 : ℝ))
      (E := (cell12472 ⟨30, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (83038780962217 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (114029665841 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_31 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (16600893581353 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280597330347 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨31, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (16600893581353 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280597330347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_32 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82970178867847 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280601302831 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨32, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82970178867847 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280601302831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_33 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82935913814037 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140302647291 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨33, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82935913814037 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140302647291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_34 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (20725418178517 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (228060930719 / 10000000000000 : ℝ))
      (E := (cell12472 ⟨34, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (20725418178517 / 25000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (228060930719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_35 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82867455536833 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280613283411 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨35, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82867455536833 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280613283411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_36 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (10354157781423 / 12500000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280617282941 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨36, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (10354157781423 / 12500000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280617282941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_37 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (82799092826929 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140310653347 / 50000000000000 : ℝ))
      (E := (cell12472 ⟨37, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (82799092826929 / 100000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (1140310653347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_38 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (1293202300513 / 1562500000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (57015632417 / 2500000000000 : ℝ))
      (E := (cell12472 ⟨38, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (1293202300513 / 1562500000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (57015632417 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12472_39 : CellCertificate 12472 (893171939785273 / 10000000000000000 : ℝ) (842068431404667 / 500000000000000000 : ℝ) (42542412132549 / 1250000000000000 : ℝ)
    (cell12472 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · norm_num [cell12472]
  · have h := gap_lower (n := 12472) (a := (16546165087723 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280629311991 / 100000000000000 : ℝ))
      (E := (cell12472 ⟨39, by decide⟩).energy) (xi := (42542412132549 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12472 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12472]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12472])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12472) (a := (16546165087723 / 20000000000000 : ℝ)) (b := (82595807231 / 50000000000000 : ℝ)) (q := (2280629311991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12472])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12472]

theorem cert12473_20 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83383230264797 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280420990649 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨20, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83383230264797 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280420990649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_21 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20837168899893 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570106251389 / 25000000000000 : ℝ))
      (E := (cell12473 ⟨21, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20837168899893 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570106251389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_22 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83314145273733 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280429007791 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨22, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83314145273733 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280429007791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_23 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83279639254197 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140216500751 / 50000000000000 : ℝ))
      (E := (cell12473 ⟨23, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83279639254197 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (1140216500751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_24 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (1664903150161 / 2000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570109247651 / 25000000000000 : ℝ))
      (E := (cell12473 ⟨24, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (1664903150161 / 2000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570109247651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_25 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83210700002549 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280440978773 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨25, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83210700002549 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280440978773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_26 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (41588133352559 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280445027847 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨26, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (41588133352559 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280445027847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_27 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (1662837151667 / 2000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (114022451213 / 5000000000000 : ℝ))
      (E := (cell12473 ⟨27, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (1662837151667 / 2000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (114022451213 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_28 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (41553736302501 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570113242729 / 25000000000000 : ℝ))
      (E := (cell12473 ⟨28, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (41553736302501 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (570113242729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_29 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83073111737999 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456091397483 / 20000000000000 : ℝ))
      (E := (cell12473 ⟨29, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83073111737999 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456091397483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_30 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20759693737607 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280461017847 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨30, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20759693737607 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280461017847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_31 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (83004462210539 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (91218600239 / 4000000000000 : ℝ))
      (E := (cell12473 ⟨31, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (83004462210539 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (91218600239 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_32 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82970173486747 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228046901231 / 10000000000000 : ℝ))
      (E := (cell12473 ⟨32, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82970173486747 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (228046901231 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_33 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (10366988593453 / 12500000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (142529561257 / 6250000000000 : ℝ))
      (E := (cell12473 ⟨33, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (10366988593453 / 12500000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (142529561257 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_34 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (41450833980953 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280476969483 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨34, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (41450833980953 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280476969483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_35 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82867451098487 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456096196357 / 20000000000000 : ℝ))
      (E := (cell12473 ⟨35, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82867451098487 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (456096196357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_36 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (82833258126417 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (91219398381 / 4000000000000 : ℝ))
      (E := (cell12473 ⟨36, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (82833258126417 / 100000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (91219398381 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_37 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20699772253727 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280488962197 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨37, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20699772253727 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280488962197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_38 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (20691235933331 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (285061623811 / 12500000000000 : ℝ))
      (E := (cell12473 ⟨38, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (20691235933331 / 25000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (285061623811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12473_39 : CellCertificate 12473 (446571507701841 / 5000000000000000 : ℝ) (1684001795009531 / 1000000000000000000 : ℝ) (340311315710497 / 10000000000000000 : ℝ)
    (cell12473 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · norm_num [cell12473]
  · have h := gap_lower (n := 12473) (a := (41365411125593 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280496986161 / 100000000000000 : ℝ))
      (E := (cell12473 ⟨39, by decide⟩).energy) (xi := (340311315710497 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12473 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12473]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12473])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12473) (a := (41365411125593 / 50000000000000 : ℝ)) (b := (82589100897 / 50000000000000 : ℝ)) (q := (2280496986161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12473])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12473]

theorem cert12474_20 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (2605725658587 / 3125000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140144373957 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨20, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (2605725658587 / 3125000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140144373957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_21 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (16669733345903 / 20000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280292730183 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨21, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (16669733345903 / 20000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280292730183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_22 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (5207133545199 / 6250000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280296758803 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨22, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (5207133545199 / 6250000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280296758803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_23 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (8327963102271 / 10000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280300721343 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨23, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (8327963102271 / 10000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280300721343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_24 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (4162257479759 / 5000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (285038092293 / 12500000000000 : ℝ))
      (E := (cell12474 ⟨24, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (4162257479759 / 5000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (285038092293 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_25 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (20802673101963 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280308755177 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨25, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (20802673101963 / 25000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280308755177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_26 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (1663525188563 / 2000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280312716889 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨26, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (1663525188563 / 2000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280312716889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_27 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83141850623669 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280316743451 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨27, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83141850623669 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280316743451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_28 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41553732981083 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280320721019 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨28, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41553732981083 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280320721019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_29 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83073105411567 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (285040588841 / 12500000000000 : ℝ))
      (E := (cell12474 ⟨29, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83073105411567 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (285040588841 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_30 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (83038768939959 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140164357543 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨30, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (83038768939959 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140164357543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_31 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (16600891303119 / 20000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280332736367 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨31, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (16600891303119 / 20000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280332736367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_32 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82970168106889 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1781513061 / 78125000000 : ℝ))
      (E := (cell12474 ⟨32, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82970168106889 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1781513061 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_33 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (5183493980151 / 6250000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570085180133 / 25000000000000 : ℝ))
      (E := (cell12474 ⟨33, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (5183493980151 / 6250000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (570085180133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_34 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (8290166321091 / 10000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140172372657 / 50000000000000 : ℝ))
      (E := (cell12474 ⟨34, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (8290166321091 / 10000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (1140172372657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_35 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82867446661267 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280348735177 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨35, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82867446661267 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280348735177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_36 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82833254002539 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280352691189 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨36, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82833254002539 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280352691189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_37 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (2587471412623 / 3125000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280356731499 / 100000000000000 : ℝ))
      (E := (cell12474 ⟨37, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (2587471412623 / 3125000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (2280356731499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_38 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (41382470117413 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (142522546219 / 6250000000000 : ℝ))
      (E := (cell12474 ⟨38, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (41382470117413 / 50000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (142522546219 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

theorem cert12474_39 : CellCertificate 12474 (89311409548287 / 1000000000000000 : ℝ) (420966687218217 / 250000000000000000 : ℝ) (340283339049267 / 10000000000000000 : ℝ)
    (cell12474 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · norm_num [cell12474]
  · have h := gap_lower (n := 12474) (a := (82730819064729 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (5700911789 / 250000000000 : ℝ))
      (E := (cell12474 ⟨39, by decide⟩).energy) (xi := (340283339049267 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12474 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12474]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12474])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12474) (a := (82730819064729 / 100000000000000 : ℝ)) (b := (6606591653 / 4000000000000 : ℝ)) (q := (5700911789 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12474])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12474]

end BstLean.Part268
