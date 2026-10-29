import BstLean.Part268CellShard1Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12375_20 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (3335365570879 / 4000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146826479617 / 50000000000000 : ℝ))
      (E := (cell12375 ⟨20, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (3335365570879 / 4000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146826479617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_21 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41674776528923 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (286707124043 / 12500000000000 : ℝ))
      (E := (cell12375 ⟨21, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41674776528923 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (286707124043 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_22 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83314991227203 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293660938899 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨22, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83314991227203 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293660938899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_23 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (26649745199 / 32000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (14335406113 / 625000000000 : ℝ))
      (E := (cell12375 ⟨23, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (26649745199 / 32000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (14335406113 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_24 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83245940583859 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293668939081 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨24, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83245940583859 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293668939081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_25 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (3328458068213 / 4000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (143354558899 / 6250000000000 : ℝ))
      (E := (cell12375 ⟨25, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (3328458068213 / 4000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (143354558899 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_26 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83176987078611 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (229367693327 / 10000000000000 : ℝ))
      (E := (cell12375 ⟨26, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83176987078611 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (229367693327 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_27 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83142546671223 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458736183019 / 20000000000000 : ℝ))
      (E := (cell12375 ⟨27, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83142546671223 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458736183019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_28 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (5194258153177 / 6250000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146842474709 / 50000000000000 : ℝ))
      (E := (cell12375 ⟨28, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (5194258153177 / 6250000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146842474709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_29 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41536869192639 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (143355557643 / 6250000000000 : ℝ))
      (E := (cell12375 ⟨29, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41536869192639 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (143355557643 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_30 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83039370442563 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573423238313 / 25000000000000 : ℝ))
      (E := (cell12375 ⟨30, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83039370442563 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573423238313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_31 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (16601005318171 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146848463901 / 50000000000000 : ℝ))
      (E := (cell12375 ⟨31, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (16601005318171 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146848463901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_32 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82970706798483 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (229370090659 / 10000000000000 : ℝ))
      (E := (cell12375 ⟨32, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82970706798483 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (229370090659 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_33 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41468205516969 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146852445793 / 50000000000000 : ℝ))
      (E := (cell12375 ⟨33, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41468205516969 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146852445793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_34 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41451069632937 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293708943099 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨34, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41451069632937 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293708943099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_35 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82867891463101 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293712886921 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨35, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82867891463101 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293712886921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_36 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (2588552112331 / 3125000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (286714612507 / 12500000000000 : ℝ))
      (E := (cell12375 ⟨36, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (2588552112331 / 3125000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (286714612507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_37 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82799467629473 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (35839389453 / 1562500000000 : ℝ))
      (E := (cell12375 ⟨37, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82799467629473 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (35839389453 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_38 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82765291537033 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573431225973 / 25000000000000 : ℝ))
      (E := (cell12375 ⟨38, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82765291537033 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573431225973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_39 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (82731139286711 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293728895987 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨39, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (82731139286711 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293728895987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12376_20 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83384129911839 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573378768833 / 25000000000000 : ℝ))
      (E := (cell12376 ⟨20, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83384129911839 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573378768833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_21 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83349544021583 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293519069347 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨21, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83349544021583 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293519069347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_22 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (2082874562859 / 2500000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293523035827 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨22, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (2082874562859 / 2500000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293523035827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_23 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83280445356999 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293527037393 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨23, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83280445356999 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293527037393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_24 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83245932516501 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146765509921 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨24, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83245932516501 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146765509921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_25 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83211443960033 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (286691880671 / 12500000000000 : ℝ))
      (E := (cell12376 ⟨25, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83211443960033 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (286691880671 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_26 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83176979654937 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (458707811849 / 20000000000000 : ℝ))
      (E := (cell12376 ⟨26, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83176979654937 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (458707811849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_27 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83142539568717 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146771503213 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨27, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83142539568717 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146771503213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_28 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (10388515458631 / 12500000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146773503413 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨28, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (10388515458631 / 12500000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146773503413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_29 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (10384216490471 / 12500000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (286693875619 / 12500000000000 : ℝ))
      (E := (cell12376 ⟨29, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (10384216490471 / 12500000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (286693875619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_30 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41519682150441 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293555003461 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨30, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41519682150441 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293555003461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_31 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41502510384279 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293559004779 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨31, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41502510384279 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293559004779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_32 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41485350647563 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146781505551 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨32, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41485350647563 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146781505551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_33 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41468202924539 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293567024397 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨33, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41468202924539 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293567024397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_34 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20725533599767 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573392746957 / 25000000000000 : ℝ))
      (E := (cell12376 ⟨34, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20725533599767 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573392746957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_35 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20716971728477 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (229357502003 / 10000000000000 : ℝ))
      (E := (cell12376 ⟨35, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20716971728477 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (229357502003 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_36 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82833663362571 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146789502557 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨36, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82833663362571 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146789502557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_37 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (16559892742837 / 20000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293583002713 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨37, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (16559892742837 / 20000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293583002713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_38 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (82765287938037 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (114679350683 / 5000000000000 : ℝ))
      (E := (cell12376 ⟨38, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (82765287938037 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (114679350683 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_39 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (8273113600357 / 10000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (71674718121 / 3125000000000 : ℝ))
      (E := (cell12376 ⟨39, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (8273113600357 / 10000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (71674718121 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12377_20 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83384120553461 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146688622679 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨20, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83384120553461 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146688622679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_21 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83349534987037 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (286672650043 / 12500000000000 : ℝ))
      (E := (cell12377 ⟨21, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83349534987037 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (286672650043 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_22 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41657486901597 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146692593407 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨22, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41657486901597 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146692593407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_23 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83280436968761 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (286673651143 / 12500000000000 : ℝ))
      (E := (cell12377 ⟨23, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83280436968761 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (286673651143 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_24 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83245924450739 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (229339321313 / 10000000000000 : ℝ))
      (E := (cell12377 ⟨24, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83245924450739 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (229339321313 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_25 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41605718108149 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293397202603 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨25, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41605718108149 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293397202603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_26 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83176972232779 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293401181153 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨26, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83176972232779 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293401181153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_27 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (10392816558461 / 12500000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573351302637 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨27, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (10392816558461 / 12500000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573351302637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_28 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (831081168887 / 1000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146704588557 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨28, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (831081168887 / 1000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146704588557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_29 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (16614745092731 / 20000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (286676650073 / 12500000000000 : ℝ))
      (E := (cell12377 ⟨29, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (16614745092731 / 20000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (286676650073 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_30 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83039358160559 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573354291681 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨30, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83039358160559 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573354291681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_31 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83005014947579 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146710597449 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨31, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83005014947579 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146710597449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_32 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82970695793047 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573356292579 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨32, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82970695793047 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573356292579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_33 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (5183525041591 / 6250000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146714576713 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨33, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (5183525041591 / 6250000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146714576713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_34 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (4145106476673 / 5000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573358286491 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨34, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (4145106476673 / 5000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573358286491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_35 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41433941182937 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293437149437 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨35, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41433941182937 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293437149437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_36 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82833659131669 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573360291283 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨36, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82833659131669 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573360291283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_37 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (3311978391999 / 4000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (114672256773 / 5000000000000 : ℝ))
      (E := (cell12377 ⟨37, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (3311978391999 / 4000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (114672256773 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_38 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (82765284340081 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293449178517 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨38, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (82765284340081 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293449178517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_39 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (8273113272143 / 10000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (358352059 / 15625000000 : ℝ))
      (E := (cell12377 ⟨39, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (8273113272143 / 10000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (358352059 / 15625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12378_20 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (2084602779921 / 2500000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (17915932899 / 781250000000 : ℝ))
      (E := (cell12378 ⟨20, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (2084602779921 / 2500000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (17915932899 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_21 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (2604672686069 / 3125000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146621721803 / 50000000000000 : ℝ))
      (E := (cell12378 ⟨21, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (2604672686069 / 3125000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146621721803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_22 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (10414370636713 / 12500000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458649490031 / 20000000000000 : ℝ))
      (E := (cell12378 ⟨22, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (10414370636713 / 12500000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458649490031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_23 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83280428582159 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293251435021 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨23, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83280428582159 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293251435021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_24 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83245916386573 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293255402271 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨24, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83245916386573 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293255402271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_25 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83211428474119 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146629707047 / 50000000000000 : ℝ))
      (E := (cell12378 ⟨25, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83211428474119 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146629707047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_26 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83176964812137 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293263415767 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨26, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83176964812137 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293263415767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_27 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (16628505073627 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458653482129 / 20000000000000 : ℝ))
      (E := (cell12378 ⟨27, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (16628505073627 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458653482129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_28 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (20777027527447 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573317850463 / 25000000000000 : ℝ))
      (E := (cell12378 ⟨28, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (20777027527447 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573317850463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_29 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83073719004939 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (143329712017 / 6250000000000 : ℝ))
      (E := (cell12378 ⟨29, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83073719004939 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (143329712017 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_30 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83039352021591 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293279384567 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨30, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83039352021591 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293279384567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_31 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (20751252281979 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573320845289 / 25000000000000 : ℝ))
      (E := (cell12378 ⟨31, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (20751252281979 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (573320845289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_32 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (20742672573061 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293287384239 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨32, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (20742672573061 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293287384239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_33 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82936395483071 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293291395777 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨33, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82936395483071 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293291395777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_34 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (1658042493381 / 2000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146647679467 / 50000000000000 : ℝ))
      (E := (cell12378 ⟨34, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (1658042493381 / 2000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146647679467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_35 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (82867877818997 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293299392343 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨35, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (82867877818997 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293299392343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_36 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (16566730980377 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146651690057 / 50000000000000 : ℝ))
      (E := (cell12378 ⟨36, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (16566730980377 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146651690057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_37 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (16559891177369 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293307381877 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨37, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (16559891177369 / 20000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293307381877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_38 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (41382640371583 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (35832990601 / 1562500000000 : ℝ))
      (E := (cell12378 ⟨38, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (41382640371583 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (35832990601 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_39 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (8273112944029 / 10000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (143332210737 / 6250000000000 : ℝ))
      (E := (cell12378 ⟨39, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (8273112944029 / 10000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (143332210737 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12379_20 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (10423012730247 / 12500000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (286637718401 / 12500000000000 : ℝ))
      (E := (cell12379 ⟨20, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (10423012730247 / 12500000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (286637718401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_21 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (10418689615387 / 12500000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458621148173 / 20000000000000 : ℝ))
      (E := (cell12379 ⟨21, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (10418689615387 / 12500000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458621148173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_22 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83314956385891 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458621941853 / 20000000000000 : ℝ))
      (E := (cell12379 ⟨22, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83314956385891 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458621941853 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_23 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83280420197193 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146556857513 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨23, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83280420197193 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146556857513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_24 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83245908324003 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293117703943 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨24, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83245908324003 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293117703943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_25 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (10401427591687 / 12500000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146560839921 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨25, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (10401427591687 / 12500000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146560839921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_26 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (8317695739301 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293125704703 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨26, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (8317695739301 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293125704703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_27 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83142518270057 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293129665129 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨27, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83142518270057 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293129665129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_28 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83108103332313 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146566840519 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨28, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83108103332313 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146566840519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_29 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41536856273809 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293137696933 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨29, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41536856273809 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293137696933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_30 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (4151967294199 / 5000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293141656987 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨30, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (4151967294199 / 5000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293141656987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_31 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83005003309569 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146572840281 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨31, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83005003309569 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146572840281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_32 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41485342396359 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (573287413217 / 25000000000000 : ℝ))
      (E := (cell12379 ⟨32, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41485342396359 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (573287413217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_33 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82936390301923 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293153692899 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨33, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82936390301923 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293153692899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_34 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41451059902919 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146578842657 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨34, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41451059902919 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146578842657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_35 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82867873273279 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293161690147 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨35, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82867873273279 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293161690147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_36 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (4141682533661 / 5000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293165650059 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨36, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (4141682533661 / 5000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293165650059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_37 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41399725987397 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293169683323 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨37, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41399725987397 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293169683323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_38 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (8276527714729 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (71661677297 / 3125000000000 : ℝ))
      (E := (cell12379 ⟨38, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (8276527714729 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (71661677297 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_39 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (82731126160151 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293177679831 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨39, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (82731126160151 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293177679831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12380_20 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (20846023122217 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146482039517 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨20, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (20846023122217 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146482039517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_21 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (833495078937 / 1000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458593606771 / 20000000000000 : ℝ))
      (E := (cell12380 ⟨21, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (833495078937 / 1000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458593606771 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_22 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41657473839877 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (573243020183 / 25000000000000 : ℝ))
      (E := (cell12380 ⟨22, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41657473839877 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (573243020183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_23 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41640205906931 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292976049159 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨23, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41640205906931 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292976049159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_24 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83245900263029 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (71655626869 / 3125000000000 : ℝ))
      (E := (cell12380 ⟨24, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83245900263029 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (71655626869 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_25 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83211412994427 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (573246014553 / 25000000000000 : ℝ))
      (E := (cell12380 ⟨25, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83211412994427 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (573246014553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_26 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83176949975399 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292988047961 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨26, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83176949975399 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292988047961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_27 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (16628502234691 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (229299203241 / 10000000000000 : ℝ))
      (E := (cell12380 ⟨27, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (16628502234691 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (229299203241 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_28 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (5194256034767 / 6250000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146498007339 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨28, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (5194256034767 / 6250000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146498007339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_29 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83073706091693 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293000056109 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨29, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83073706091693 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293000056109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_30 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (20759834936931 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293004042469 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨30, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (20759834936931 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293004042469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_31 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41502498746269 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293008034613 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨31, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41502498746269 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293008034613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_32 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82970679294469 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146506017367 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨32, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82970679294469 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146506017367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_33 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82936385122011 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (573254011199 / 25000000000000 : ℝ))
      (E := (cell12380 ⟨33, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82936385122011 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (573254011199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_34 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41451057471911 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146510003979 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨34, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41451057471911 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146510003979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_35 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41433934364359 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (17914249877 / 781250000000 : ℝ))
      (E := (cell12380 ⟨35, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41433934364359 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (17914249877 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_36 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41416823222837 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (229302803359 / 10000000000000 : ℝ))
      (E := (cell12380 ⟨36, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41416823222837 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (229302803359 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_37 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41399724031911 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293031981153 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨37, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41399724031911 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293031981153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_38 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82765273552453 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293036003637 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨38, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82765273552453 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2293036003637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_39 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (82731122881013 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458607996867 / 20000000000000 : ℝ))
      (E := (cell12380 ⟨39, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (82731122881013 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458607996867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12381_20 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (20846020784379 / 25000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458565292959 / 20000000000000 : ℝ))
      (E := (cell12381 ⟨20, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (20846020784379 / 25000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458565292959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_21 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83349498866019 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292830497383 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨21, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83349498866019 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292830497383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_22 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (20828734743823 / 25000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292834447971 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨22, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (20828734743823 / 25000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292834447971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_23 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83280403432167 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146419218711 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨23, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83280403432167 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146419218711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_24 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (1664917844073 / 2000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292842469867 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨24, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (1664917844073 / 2000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292842469867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_25 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (41605702628457 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292846432477 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨25, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (41605702628457 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292846432477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_26 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83176942559303 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146425222771 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨26, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83176942559303 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146425222771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_27 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (10392813009791 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146427227039 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨27, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (10392813009791 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146427227039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_28 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83108089781667 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146429230601 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨28, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83108089781667 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146429230601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_29 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (41536849818581 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292862469803 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨29, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (41536849818581 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292862469803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_30 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (10379916701603 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (573216606013 / 25000000000000 : ℝ))
      (E := (cell12381 ⟨30, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (10379916701603 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (573216606013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_31 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83004991676823 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292870443309 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨31, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83004991676823 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292870443309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_32 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (16594134759499 / 20000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146437206391 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨32, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (16594134759499 / 20000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146437206391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_33 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (10367047492917 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146439225733 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨33, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (10367047492917 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146439225733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_34 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82902110083003 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458576488803 / 20000000000000 : ℝ))
      (E := (cell12381 ⟨34, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82902110083003 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458576488803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_35 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (41433932092657 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292886450463 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨35, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (41433932092657 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292886450463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_36 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (16566728443849 / 20000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292890413467 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨36, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (16566728443849 / 20000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292890413467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_37 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (10349930519241 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292894392659 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨37, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (10349930519241 / 12500000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292894392659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_38 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (5051591184 / 6103515625 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (17913268663 / 781250000000 : ℝ))
      (E := (cell12381 ⟨38, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (5051591184 / 6103515625 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (17913268663 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_39 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (82731119602873 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (229290240269 / 10000000000000 : ℝ))
      (E := (cell12381 ⟨39, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (82731119602873 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (229290240269 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12382_20 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (1042300922349 / 1250000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146344481369 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨20, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (1042300922349 / 1250000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146344481369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_21 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41674744920027 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (573173239161 / 25000000000000 : ℝ))
      (E := (cell12382 ⟨21, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41674744920027 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (573173239161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_22 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16662986054501 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (229269692757 / 10000000000000 : ℝ))
      (E := (cell12382 ⟨22, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16662986054501 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (229269692757 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_23 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83280395052107 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (573175234533 / 25000000000000 : ℝ))
      (E := (cell12382 ⟨23, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83280395052107 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (573175234533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_24 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16649176829173 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292704934123 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨24, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16649176829173 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292704934123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_25 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16642279504191 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146354459683 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨25, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16642279504191 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146354459683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_26 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83176935144721 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (45854257949 / 2000000000000 : ℝ))
      (E := (cell12382 ⟨26, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83176935144721 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (45854257949 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_27 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (3325699879387 / 4000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292716930137 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨27, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (3325699879387 / 4000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292716930137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_28 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (5194255188031 / 6250000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (573180225937 / 25000000000000 : ℝ))
      (E := (cell12382 ⟨28, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (5194255188031 / 6250000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (573180225937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_29 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83073693184027 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458544987603 / 20000000000000 : ℝ))
      (E := (cell12382 ⟨29, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83073693184027 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458544987603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_30 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41519663739639 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292728918699 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨30, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41519663739639 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292728918699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_31 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83004985862423 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292732906653 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨31, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83004985862423 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292732906653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_32 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (20742667075449 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292736904071 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨32, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (20742667075449 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292736904071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_33 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (10367046845737 / 12500000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (143296307057 / 6250000000000 : ℝ))
      (E := (cell12382 ⟨33, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (10367046845737 / 12500000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (143296307057 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_34 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (82902105223381 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (143296554771 / 6250000000000 : ℝ))
      (E := (cell12382 ⟨34, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (82902105223381 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (143296554771 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_35 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (82867859643067 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (91709956519 / 4000000000000 : ℝ))
      (E := (cell12382 ⟨35, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (82867859643067 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (91709956519 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_36 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (82833637993933 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146376453467 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨36, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (82833637993933 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146376453467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_37 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (10349930030639 / 12500000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292756917841 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨37, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (10349930030639 / 12500000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292756917841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_38 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (82765266365897 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458552177571 / 20000000000000 : ℝ))
      (E := (cell12382 ⟨38, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (82765266365897 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458552177571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_39 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41365558162867 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292764876203 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨39, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41365558162867 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292764876203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12383_20 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83384064440079 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146275728187 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨20, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83384064440079 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146275728187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_21 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83349480815803 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292555469909 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨21, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83349480815803 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292555469909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_22 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (1301795649553 / 1562500000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292559461237 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨22, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (1301795649553 / 1562500000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292559461237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_23 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (1041004833421 / 1250000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (143285218311 / 6250000000000 : ℝ))
      (E := (cell12383 ⟨23, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (1041004833421 / 1250000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (143285218311 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_24 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (3329835043587 / 4000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (71642732893 / 3125000000000 : ℝ))
      (E := (cell12383 ⟨24, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (3329835043587 / 4000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (71642732893 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_25 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83211389786551 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292571460517 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨25, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83211389786551 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292571460517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_26 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41588463865827 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (229257546207 / 10000000000000 : ℝ))
      (E := (cell12383 ⟨26, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41588463865827 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (229257546207 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_27 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83142489892497 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146289730293 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨27, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83142489892497 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146289730293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_28 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83108076236759 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (143286466199 / 6250000000000 : ℝ))
      (E := (cell12383 ⟨28, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83108076236759 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (143286466199 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_29 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41536843366143 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (573146865187 / 25000000000000 : ℝ))
      (E := (cell12383 ⟨29, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41536843366143 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (573146865187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_30 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83039321347087 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (229259146793 / 10000000000000 : ℝ))
      (E := (cell12383 ⟨30, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83039321347087 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (229259146793 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_31 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41502490024669 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458519084929 / 20000000000000 : ℝ))
      (E := (cell12383 ⟨31, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41502490024669 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458519084929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_32 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82970662807373 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292599450071 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨32, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82970662807373 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292599450071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_33 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (20734092397423 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (143287714321 / 6250000000000 : ℝ))
      (E := (cell12383 ⟨33, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (20734092397423 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (143287714321 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_34 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41451050182477 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146303711037 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨34, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41451050182477 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146303711037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_35 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82867855101977 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292611430393 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨35, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82867855101977 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292611430393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_36 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41416816884869 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (229261545537 / 10000000000000 : ℝ))
      (E := (cell12383 ⟨36, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41416816884869 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (229261545537 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_37 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41399718168687 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (573154859853 / 25000000000000 : ℝ))
      (E := (cell12383 ⟨37, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41399718168687 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (573154859853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_38 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (2586414461693 / 3125000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458524688389 / 20000000000000 : ℝ))
      (E := (cell12383 ⟨38, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (2586414461693 / 3125000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458524688389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_39 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (82731113049593 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146313702439 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨39, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (82731113049593 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146313702439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12384_20 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83384055093993 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458482812439 / 20000000000000 : ℝ))
      (E := (cell12384 ⟨20, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83384055093993 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458482812439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_21 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83349471793267 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146209047723 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨21, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83349471793267 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146209047723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_22 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83314912871953 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146211024487 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨22, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83314912871953 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146211024487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_23 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (10410047287111 / 12500000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292426043637 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨23, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (10410047287111 / 12500000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292426043637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_24 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41622934017539 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143276880223 / 6250000000000 : ℝ))
      (E := (cell12384 ⟨24, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41622934017539 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143276880223 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_25 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (832113820537 / 1000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (573108513983 / 25000000000000 : ℝ))
      (E := (cell12384 ⟨25, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (832113820537 / 1000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (573108513983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_26 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (831769203201 / 1000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146219040509 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨26, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (831769203201 / 1000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146219040509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_27 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (649550646889 / 781250000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292442045429 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨27, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (649550646889 / 781250000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292442045429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_28 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (10388508683307 / 12500000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292446069077 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨28, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (10388508683307 / 12500000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292446069077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_29 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83073680281939 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146225019001 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨29, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83073680281939 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146225019001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_30 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83039315216251 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146227035873 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨30, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83039315216251 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146227035873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_31 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83004974237567 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143278628487 / 6250000000000 : ℝ))
      (E := (cell12384 ⟨31, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83004974237567 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143278628487 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_32 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (3318826292569 / 4000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146231025393 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨32, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (3318826292569 / 4000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146231025393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_33 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (20734091103681 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (35819782167 / 1562500000000 : ℝ))
      (E := (cell12384 ⟨33, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (20734091103681 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (35819782167 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_34 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82902095507723 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458494004531 / 20000000000000 : ℝ))
      (E := (cell12384 ⟨34, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82902095507723 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458494004531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_35 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41433925281021 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146237001359 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨35, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41433925281021 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146237001359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_36 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (4141681477333 / 5000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458495600031 / 20000000000000 : ℝ))
      (E := (cell12384 ⟨36, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (4141681477333 / 5000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458495600031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_37 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82799432430713 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292482016017 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨37, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82799432430713 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292482016017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_38 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41382629591747 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292486051131 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨38, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41382629591747 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292486051131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_39 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (82731109774451 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143280627963 / 6250000000000 : ℝ))
      (E := (cell12384 ⟨39, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (82731109774451 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143280627963 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12385_20 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83384045749661 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292276721957 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨20, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83384045749661 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292276721957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_21 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (16669892554489 / 20000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (28653508959 / 1250000000000 : ℝ))
      (E := (cell12385 ⟨21, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (16669892554489 / 20000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (28653508959 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_22 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83314904174189 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (143267796817 / 6250000000000 : ℝ))
      (E := (cell12385 ⟨22, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83314904174189 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (143267796817 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_23 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83280369921729 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (9169154827 / 400000000000 : ℝ))
      (E := (cell12385 ⟨23, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83280369921729 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (9169154827 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_24 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41622929991037 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (114614635521 / 5000000000000 : ℝ))
      (E := (cell12385 ⟨24, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41622929991037 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (114614635521 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_25 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41605687161201 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292296705611 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨25, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41605687161201 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292296705611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_26 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83176912910059 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292300695909 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨26, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83176912910059 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292300695909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_27 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (1039280946407 / 1250000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (91692189723 / 4000000000000 : ℝ))
      (E := (cell12385 ⟨27, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (1039280946407 / 1250000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (91692189723 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_28 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41554031348793 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292308733427 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨28, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41554031348793 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292308733427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_29 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (16614734766597 / 20000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458462545647 / 20000000000000 : ℝ))
      (E := (cell12385 ⟨29, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (16614734766597 / 20000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458462545647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_30 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (5189956817923 / 6250000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (45846334603 / 2000000000000 : ℝ))
      (E := (cell12385 ⟨30, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (5189956817923 / 6250000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (45846334603 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_31 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (8300496842711 / 10000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146160341543 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨31, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (8300496842711 / 10000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146160341543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_32 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82970651822351 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (286540588277 / 12500000000000 : ℝ))
      (E := (cell12385 ⟨32, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82970651822351 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (286540588277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_33 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (8293635924099 / 10000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573082171117 / 25000000000000 : ℝ))
      (E := (cell12385 ⟨33, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (8293635924099 / 10000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573082171117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_34 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82902090651687 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146166339039 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨34, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82902090651687 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146166339039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_35 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (2589620188227 / 3125000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573084172137 / 25000000000000 : ℝ))
      (E := (cell12385 ⟨35, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (2589620188227 / 3125000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573084172137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_36 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82833625324699 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146170358577 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨36, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82833625324699 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146170358577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_37 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82799428525129 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292344706303 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨37, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82799428525129 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292344706303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_38 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (82765255593849 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573087164187 / 25000000000000 : ℝ))
      (E := (cell12385 ⟨38, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (82765255593849 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (573087164187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_39 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (20682776625077 / 25000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292352686407 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨39, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (20682776625077 / 25000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292352686407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12386_20 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83384036407083 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146069746953 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨20, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83384036407083 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146069746953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_21 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (10418681719167 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (229214345027 / 10000000000000 : ℝ))
      (E := (cell12386 ⟨21, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (10418681719167 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (229214345027 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_22 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83314895478097 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (45842948899 / 2000000000000 : ℝ))
      (E := (cell12386 ⟨22, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83314895478097 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (45842948899 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_23 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83280361548203 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458430296463 / 20000000000000 : ℝ))
      (E := (cell12386 ⟨23, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83280361548203 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458430296463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_24 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (10405731491333 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573038862453 / 25000000000000 : ℝ))
      (E := (cell12386 ⟨24, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (10405731491333 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573038862453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_25 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83211366592657 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292159467919 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨25, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83211366592657 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292159467919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_26 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83176905501531 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292163423517 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨26, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83176905501531 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292163423517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_27 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83142468624801 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146083718353 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨27, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83142468624801 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146083718353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_28 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (1662161118603 / 2000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573042863059 / 25000000000000 : ℝ))
      (E := (cell12386 ⟨28, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (1662161118603 / 2000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573042863059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_29 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (3322946695417 / 4000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146087707267 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨29, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (3322946695417 / 4000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146087707267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_30 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41519651479319 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292179443141 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨30, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41519651479319 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292179443141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_31 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (5187810163623 / 6250000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458436684707 / 20000000000000 : ℝ))
      (E := (cell12386 ⟨31, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (5187810163623 / 6250000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458436684707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_32 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82970646331751 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292187416363 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨32, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82970646331751 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292187416363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_33 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82936354068491 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (114609571179 / 5000000000000 : ℝ))
      (E := (cell12386 ⟨33, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82936354068491 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (114609571179 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_34 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82902085796847 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292195446921 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨34, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82902085796847 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292195446921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_35 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82867841485641 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146099714643 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨35, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82867841485641 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146099714643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_36 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41416810551927 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286525428813 / 12500000000000 : ℝ))
      (E := (cell12386 ⟨36, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41416810551927 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286525428813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_37 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82799424620623 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146103696489 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨37, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82799424620623 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146103696489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_38 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41382626002621 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292211434803 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨38, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41382626002621 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292211434803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_39 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (82731103227163 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (229221538057 / 10000000000000 : ℝ))
      (E := (cell12386 ⟨39, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (82731103227163 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (229221538057 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12387_20 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83384027066257 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573000565389 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨20, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83384027066257 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573000565389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_21 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (4167472236797 / 5000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (229200623783 / 10000000000000 : ℝ))
      (E := (cell12387 ⟨21, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (4167472236797 / 5000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (229200623783 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_22 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41657443391839 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573002563299 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨22, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41657443391839 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573002563299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_23 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (8328035317631 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292014253703 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨23, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (8328035317631 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292014253703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_24 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41622921940423 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (143251140213 / 6250000000000 : ℝ))
      (E := (cell12387 ⟨24, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41622921940423 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (143251140213 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_25 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (16642271772893 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573005556533 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨25, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (16642271772893 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573005556533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_26 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (20794224523629 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292026205457 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨26, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (20794224523629 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292026205457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_27 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (16628492307703 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (286503780393 / 12500000000000 : ℝ))
      (E := (cell12387 ⟨27, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (16628492307703 / 20000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (286503780393 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_28 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41554024582073 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573008556377 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨28, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41554024582073 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573008556377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_29 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83073660939257 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1146019106909 / 50000000000000 : ℝ))
      (E := (cell12387 ⟨29, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83073660939257 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1146019106909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_30 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41519648415931 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292042210723 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨30, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41519648415931 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292042210723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_31 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41502478405069 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (28650577733 / 1250000000000 : ℝ))
      (E := (cell12387 ⟨31, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41502478405069 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (28650577733 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_32 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (3318825633697 / 4000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573012559939 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨32, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (3318825633697 / 4000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573012559939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_33 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41468174448613 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573013554369 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨33, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41468174448613 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573013554369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_34 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (82902080943201 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573014553009 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨34, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (82902080943201 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573014553009 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_35 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41433918474587 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (286507778117 / 12500000000000 : ℝ))
      (E := (cell12387 ⟨35, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41433918474587 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (286507778117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_36 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (20708404221031 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292066198829 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨36, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (20708404221031 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292066198829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_37 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (10349927589649 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (114603509667 / 5000000000000 : ℝ))
      (E := (cell12387 ⟨37, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (10349927589649 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (114603509667 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_38 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (10345656052209 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573018552323 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨38, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (10345656052209 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (573018552323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_39 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (10341387494377 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292078188593 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨39, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (10341387494377 / 12500000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2292078188593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12388_20 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (16676803545437 / 20000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291865083149 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨20, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (16676803545437 / 20000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291865083149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_21 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83349435720257 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (11459345397 / 500000000000 : ℝ))
      (E := (cell12388 ⟨21, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83349435720257 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (11459345397 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_22 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83314878090931 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291873115517 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨22, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83314878090931 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291873115517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_23 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83280344806049 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291877079231 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨23, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83280344806049 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291877079231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_24 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83245835832619 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (229188109121 / 10000000000000 : ℝ))
      (E := (cell12388 ⟨24, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83245835832619 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (229188109121 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_25 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (2600354723057 / 3125000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145942548489 / 50000000000000 : ℝ))
      (E := (cell12388 ⟨25, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (2600354723057 / 3125000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145942548489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_26 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (20794222672253 / 25000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291889100119 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨26, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (20794222672253 / 25000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291889100119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_27 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83142454453701 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (114594655199 / 5000000000000 : ℝ))
      (E := (cell12388 ⟨27, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83142454453701 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (114594655199 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_28 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41554021199787 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145948526621 / 50000000000000 : ℝ))
      (E := (cell12388 ⟨28, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41554021199787 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145948526621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_29 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41536827247241 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572975266907 / 25000000000000 : ℝ))
      (E := (cell12388 ⟨29, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41536827247241 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572975266907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_30 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41519645353219 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291905091377 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨30, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41519645353219 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291905091377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_31 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41502475501811 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291909068399 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨31, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41502475501811 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291909068399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_32 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82970635354373 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291913059339 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨32, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82970635354373 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291913059339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_33 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41468171863597 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458383413231 / 20000000000000 : ℝ))
      (E := (cell12388 ⟨33, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41468171863597 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (458383413231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_34 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82902076090749 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145960515999 / 50000000000000 : ℝ))
      (E := (cell12388 ⟨34, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82902076090749 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145960515999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_35 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82867832413861 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291925075497 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨35, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82867832413861 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291925075497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_36 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (8283361266551 / 10000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (229192902213 / 10000000000000 : ℝ))
      (E := (cell12388 ⟨36, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (8283361266551 / 10000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (229192902213 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_37 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41399708407419 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291933048739 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨37, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41399708407419 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291933048739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_38 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82765244831139 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291937038883 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨38, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82765244831139 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291937038883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_39 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (82731096683867 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145970525891 / 50000000000000 : ℝ))
      (E := (cell12388 ⟨39, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (82731096683867 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145970525891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12389_20 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16676801677973 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (286466002117 / 12500000000000 : ℝ))
      (E := (cell12389 ⟨20, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16676801677973 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (286466002117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_21 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16669885341257 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291732033251 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨21, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16669885341257 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291732033251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_22 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83314869399857 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291736031913 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨22, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83314869399857 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291736031913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_23 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83280336437419 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (35808437769 / 1562500000000 : ℝ))
      (E := (cell12389 ⟨23, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83280336437419 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (35808437769 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_24 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16649165557197 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458348798643 / 20000000000000 : ℝ))
      (E := (cell12389 ⟨24, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16649165557197 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458348798643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_25 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16642268682547 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291748022093 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨25, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16642268682547 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291748022093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_26 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (4158844164251 / 5000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291751990727 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨26, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (4158844164251 / 5000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291751990727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_27 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41571223685179 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458351192161 / 20000000000000 : ℝ))
      (E := (cell12389 ⟨27, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41571223685179 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458351192161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_28 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41554017818217 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291759993873 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨28, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41554017818217 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291759993873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_29 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83073648051099 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458352795193 / 20000000000000 : ℝ))
      (E := (cell12389 ⟨29, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83073648051099 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458352795193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_30 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83039284582367 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291767968141 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨30, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83039284582367 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291767968141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_31 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41502472599209 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458354394563 / 20000000000000 : ℝ))
      (E := (cell12389 ⟨31, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41502472599209 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (458354394563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_32 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82970629867593 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291775992173 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨32, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82970629867593 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291775992173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_33 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (20734084639599 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291779969619 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨33, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (20734084639599 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291779969619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_34 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (20725517809873 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (286472995673 / 12500000000000 : ℝ))
      (E := (cell12389 ⟨34, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (20725517809873 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (286472995673 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_35 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41433913939851 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291787980971 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨35, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41433913939851 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291787980971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_36 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82833608448011 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291791959029 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨36, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82833608448011 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291791959029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_37 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (82799412913559 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (114589797959 / 5000000000000 : ℝ))
      (E := (cell12389 ⟨37, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (82799412913559 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (114589797959 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_38 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41382620622821 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291799982249 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨38, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41382620622821 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291799982249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_39 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41365546706857 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (114590198507 / 5000000000000 : ℝ))
      (E := (cell12389 ⟨39, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41365546706857 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (114590198507 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12390_20 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83383999054297 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (229159100467 / 10000000000000 : ℝ))
      (E := (cell12390 ⟨20, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83383999054297 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (229159100467 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_21 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41674708847013 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572898745711 / 25000000000000 : ℝ))
      (E := (cell12390 ⟨21, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41674708847013 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572898745711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_22 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83314860710453 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291599002387 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨22, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83314860710453 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291599002387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_23 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83280328070421 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145801475513 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨23, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83280328070421 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145801475513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_24 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41622909870471 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291606949427 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨24, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41622909870471 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291606949427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_25 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41605667844599 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458322188623 / 20000000000000 : ℝ))
      (E := (cell12390 ⟨25, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41605667844599 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458322188623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_26 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (4158843794127 / 5000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (229161493567 / 10000000000000 : ℝ))
      (E := (cell12390 ⟨26, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (4158843794127 / 5000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (229161493567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_27 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83142440288487 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (57290473261 / 2500000000000 : ℝ))
      (E := (cell12390 ⟨27, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83142440288487 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (57290473261 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_28 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41554014437363 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145811465267 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨28, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41554014437363 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145811465267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_29 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83073641609107 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (143226683677 / 6250000000000 : ℝ))
      (E := (cell12390 ⟨29, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83073641609107 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (143226683677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_30 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83039278459647 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (114581547899 / 5000000000000 : ℝ))
      (E := (cell12390 ⟨30, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83039278459647 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (114581547899 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_31 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41502469697263 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (143227183243 / 6250000000000 : ℝ))
      (E := (cell12390 ⟨31, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41502469697263 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (143227183243 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_32 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41485312191043 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291638921199 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨32, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41485312191043 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291638921199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_33 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (5183520836927 / 6250000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291642927867 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨33, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (5183520836927 / 6250000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291642927867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_34 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (20725516597357 / 25000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291646953619 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨34, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (20725516597357 / 25000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291646953619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_35 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41433911673349 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145825470679 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨35, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41433911673349 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145825470679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_36 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82833604231627 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458330990181 / 20000000000000 : ℝ))
      (E := (cell12390 ⟨36, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82833604231627 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458330990181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_37 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (20699852253339 / 25000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291658924661 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨37, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (20699852253339 / 25000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291658924661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_38 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41382618830591 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291662922049 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨38, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41382618830591 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291662922049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_39 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (82731090144559 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145833471833 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨39, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (82731090144559 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145833471833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12391_20 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83383989720481 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145727023177 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨20, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83383989720481 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145727023177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_21 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83349408683477 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291458044723 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨21, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83349408683477 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291458044723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_22 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83314852022721 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (114573101347 / 5000000000000 : ℝ))
      (E := (cell12391 ⟨22, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83314852022721 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (114573101347 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_23 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41640159852527 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291465997297 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨23, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41640159852527 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291465997297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_24 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83245811697489 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (229147001819 / 10000000000000 : ℝ))
      (E := (cell12391 ⟨24, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83245811697489 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (229147001819 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_25 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83211327967211 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (91658959071 / 4000000000000 : ℝ))
      (E := (cell12391 ⟨25, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83211327967211 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (91658959071 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_26 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (8317686848157 / 10000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (114573899667 / 5000000000000 : ℝ))
      (E := (cell12391 ⟨26, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (8317686848157 / 10000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (114573899667 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_27 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83142433208087 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (286435251611 / 12500000000000 : ℝ))
      (E := (cell12391 ⟨27, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83142433208087 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (286435251611 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_28 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83108022114449 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (35804468439 / 1562500000000 : ℝ))
      (E := (cell12391 ⟨28, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83108022114449 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (35804468439 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_29 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83073635168507 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291490014687 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨29, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83073635168507 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291490014687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_30 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (2075981808457 / 2500000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291494002413 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨30, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (2075981808457 / 2500000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291494002413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_31 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83004933591947 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (18331984033 / 800000000000 : ℝ))
      (E := (cell12391 ⟨31, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83004933591947 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (18331984033 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_32 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (20742654724463 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572875490869 / 25000000000000 : ℝ))
      (E := (cell12391 ⟨32, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (20742654724463 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572875490869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_33 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (165872656449 / 200000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (458301199891 / 20000000000000 : ℝ))
      (E := (cell12391 ⟨33, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (165872656449 / 200000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (458301199891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_34 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82902061540557 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291509996707 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨34, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82902061540557 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291509996707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_35 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (647404834491 / 781250000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291513956661 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨35, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (647404834491 / 781250000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291513956661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_36 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41416800008179 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145758969569 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨36, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41416800008179 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145758969569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_37 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (20699851278557 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291521945187 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨37, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (20699851278557 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291521945187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_38 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41382617038879 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291525975627 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨38, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41382617038879 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291525975627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_39 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (82731086876401 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291529972363 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨39, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (82731086876401 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291529972363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12392_20 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (16676796077683 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229131714199 / 10000000000000 : ℝ))
      (E := (cell12392 ⟨20, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (16676796077683 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229131714199 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_21 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (1041867495933 / 1250000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145660551173 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨21, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (1041867495933 / 1250000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145660551173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_22 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83314843336659 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145662552787 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨22, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83314843336659 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145662552787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_23 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83280311341317 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145664548857 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨23, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83280311341317 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145664548857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_24 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83245803655627 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291333082821 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨24, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83245803655627 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291333082821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_25 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41605660123387 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145668561537 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨25, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41605660123387 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145668561537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_26 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83176861082111 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572835276337 / 25000000000000 : ℝ))
      (E := (cell12392 ⟨26, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83176861082111 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572835276337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_27 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83142426129157 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229134509133 / 10000000000000 : ℝ))
      (E := (cell12392 ⟨27, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83142426129157 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229134509133 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_28 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41554007677801 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145674542063 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨28, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41554007677801 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145674542063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_29 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41536814364649 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (286419135827 / 12500000000000 : ℝ))
      (E := (cell12392 ⟨29, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41536814364649 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (286419135827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_30 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83039266218263 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572839275361 / 25000000000000 : ℝ))
      (E := (cell12392 ⟨30, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83039266218263 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572839275361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_31 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83004927790679 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145680536259 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨31, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83004927790679 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145680536259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_32 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82970613414889 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291365060479 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨32, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82970613414889 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291365060479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_33 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (414681615297 / 500000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291369067281 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨33, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (414681615297 / 500000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291369067281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_34 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82902056692879 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (286421636831 / 12500000000000 : ℝ))
      (E := (cell12392 ⟨34, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82902056692879 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (286421636831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_35 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82867814284151 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (57284427137 / 2500000000000 : ℝ))
      (E := (cell12392 ⟨35, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82867814284151 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (57284427137 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_36 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82833595802203 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (91655241639 / 4000000000000 : ℝ))
      (E := (cell12392 ⟨36, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82833595802203 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (91655241639 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_37 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (3311976048647 / 4000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291385079403 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨37, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (3311976048647 / 4000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291385079403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_38 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82765230495369 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291389084313 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨38, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82765230495369 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291389084313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_39 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (82731083609239 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291393056233 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨39, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (82731083609239 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291393056233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12393_20 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (833839710581 / 1000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291180291577 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨20, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (833839710581 / 1000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291180291577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_21 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (10418673833439 / 12500000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145592136129 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨21, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (10418673833439 / 12500000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145592136129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_22 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (20828708663067 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (143199264893 / 6250000000000 : ℝ))
      (E := (cell12393 ⟨22, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (20828708663067 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (143199264893 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_23 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (8328030297921 / 10000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572798063069 / 25000000000000 : ℝ))
      (E := (cell12393 ⟨23, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (8328030297921 / 10000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572798063069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_24 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (16649159123071 / 20000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291196260003 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨24, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (16649159123071 / 20000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291196260003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_25 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83211312527887 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572800066321 / 25000000000000 : ℝ))
      (E := (cell12393 ⟨25, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83211312527887 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572800066321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_26 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83176853684161 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291204271697 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨26, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83176853684161 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291204271697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_27 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41571209525849 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145604112087 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨27, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41571209525849 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145604112087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_28 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41554004299093 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (18329697941 / 800000000000 : ℝ))
      (E := (cell12393 ⟨28, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41554004299093 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (18329697941 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_29 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83073622291479 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291216213079 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨29, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83073622291479 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291216213079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_30 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83039260099597 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (71600632971 / 3125000000000 : ℝ))
      (E := (cell12393 ⟨30, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83039260099597 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (71600632971 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_31 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41502460995361 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291224254077 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨31, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41502460995361 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291224254077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_32 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41485303966599 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291228212207 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨32, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41485303966599 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291228212207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_33 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82936317895533 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (17900251941 / 781250000000 : ℝ))
      (E := (cell12393 ⟨33, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82936317895533 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (17900251941 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_34 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41451025923197 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145618123721 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨34, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41451025923197 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145618123721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_35 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (5179238109663 / 6250000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (286405026327 / 12500000000000 : ℝ))
      (E := (cell12393 ⟨35, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (5179238109663 / 6250000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (286405026327 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_36 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82833591589161 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291244197793 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨36, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82833591589161 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291244197793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_37 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (82799397319197 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291248210017 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨37, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (82799397319197 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291248210017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_38 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (2586413341063 / 3125000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145626094719 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨38, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (2586413341063 / 3125000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145626094719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_39 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41365540171537 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145628097637 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨39, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41365540171537 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145628097637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12394_20 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (16676792345907 / 20000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291043495117 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨20, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (16676792345907 / 20000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291043495117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_21 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (16669876332419 / 20000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291047496187 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨21, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (16669876332419 / 20000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291047496187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_22 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41657412984773 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (114552574169 / 5000000000000 : ℝ))
      (E := (cell12394 ⟨22, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41657412984773 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (114552574169 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_23 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83280294618733 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291055460987 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨23, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83280294618733 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291055460987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_24 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83245787576673 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145529745699 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨24, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83245787576673 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145529745699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_25 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (1664226096211 / 2000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291063461771 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨25, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (1664226096211 / 2000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291063461771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_26 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83176846287721 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291067492387 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨26, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83176846287721 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291067492387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_27 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (20785602993927 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572767867459 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨27, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (20785602993927 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572767867459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_28 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (415540009211 / 500000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291075455593 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨28, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (415540009211 / 500000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291075455593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_29 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83073615855051 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291079452533 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨29, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83073615855051 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291079452533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_30 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41519626991141 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145541731649 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨30, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41519626991141 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145541731649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_31 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (20751229048019 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145543715897 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨31, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (20751229048019 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145543715897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_32 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41485301226389 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (286386434649 / 12500000000000 : ℝ))
      (E := (cell12394 ⟨32, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41485301226389 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (286386434649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_33 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82936312732897 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145547712927 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨33, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82936312732897 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145547712927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_34 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82902047001101 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291099455091 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨34, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82902047001101 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291099455091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_35 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82867805226217 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (286387931159 / 12500000000000 : ℝ))
      (E := (cell12394 ⟨35, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82867805226217 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (286387931159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_36 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82833587377233 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145553734109 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨36, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82833587377233 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145553734109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_37 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82799393423293 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (91644458173 / 4000000000000 : ℝ))
      (E := (cell12394 ⟨37, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82799393423293 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (91644458173 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_38 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (82765223333697 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145557733507 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨38, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (82765223333697 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145557733507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_39 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (5170692317369 / 6250000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (286389931023 / 12500000000000 : ℝ))
      (E := (cell12394 ⟨39, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (5170692317369 / 6250000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (286389931023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12395_20 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (521149702517 / 625000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572726688153 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨20, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (521149702517 / 625000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572726688153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_21 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83349372658387 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458182154827 / 20000000000000 : ℝ))
      (E := (cell12395 ⟨21, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83349372658387 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458182154827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_22 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83314817288493 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572728695639 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨22, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83314817288493 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572728695639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_23 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (16656057251977 / 20000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290918782163 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨23, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (16656057251977 / 20000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290918782163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_24 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83245779539579 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145461388503 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨24, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83245779539579 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145461388503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_25 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41605648547381 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290926770899 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨25, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41605648547381 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290926770899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_26 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83176838892791 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145465383709 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨26, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83176838892791 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145465383709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_27 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20785601225297 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458186953981 / 20000000000000 : ℝ))
      (E := (cell12395 ⟨27, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20785601225297 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458186953981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_28 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83107995087643 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290938723033 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨28, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83107995087643 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290938723033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_29 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20768402355003 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572735686631 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨29, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20768402355003 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572735686631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_30 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83039247866317 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572736681531 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨30, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83039247866317 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572736681531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_31 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (4150245519737 / 5000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290950722681 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨31, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (4150245519737 / 5000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290950722681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_32 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (8297059697363 / 10000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145477369187 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨32, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (8297059697363 / 10000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145477369187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_33 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82936307571493 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290958716603 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨33, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82936307571493 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290958716603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_34 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82902042157 / 100000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572740679399 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨34, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82902042157 / 100000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572740679399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_35 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (82867800698979 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290966742847 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨35, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (82867800698979 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290966742847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_36 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41416791583209 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290970735003 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨36, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41416791583209 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290970735003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_37 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41399694764231 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458194939007 / 20000000000000 : ℝ))
      (E := (cell12395 ⟨37, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41399694764231 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458194939007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_38 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41382609877207 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (229097874103 / 10000000000000 : ℝ))
      (E := (cell12395 ⟨38, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41382609877207 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (229097874103 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_39 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (8273107381373 / 10000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (91639307903 / 4000000000000 : ℝ))
      (E := (cell12395 ⟨39, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (8273107381373 / 10000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (91639307903 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12396_20 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41691971538827 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (286346265289 / 12500000000000 : ℝ))
      (E := (cell12396 ⟨20, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41691971538827 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (286346265289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_21 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (20837340914097 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145387053053 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨21, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (20837340914097 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145387053053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_22 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83314808609109 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290778135819 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨22, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83314808609109 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290778135819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_23 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41640138951333 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290782099173 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨23, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41640138951333 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290782099173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_24 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41622885752037 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290786116831 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨24, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41622885752037 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290786116831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_25 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83211289380523 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (286348759493 / 12500000000000 : ℝ))
      (E := (cell12396 ⟨25, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83211289380523 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (286348759493 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_26 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83176831499369 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458158819359 / 20000000000000 : ℝ))
      (E := (cell12396 ⟨26, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83176831499369 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458158819359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_27 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (10392799728517 / 12500000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572699516493 / 25000000000000 : ℝ))
      (E := (cell12396 ⟨27, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (10392799728517 / 12500000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572699516493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_28 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (16621597666903 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145401051691 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨28, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (16621597666903 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145401051691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_29 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83073602986363 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572701523763 / 25000000000000 : ℝ))
      (E := (cell12396 ⟨29, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83073602986363 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572701523763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_30 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83039241751701 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145405051017 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨30, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83039241751701 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145405051017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_31 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (16600980919743 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290814068233 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨31, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (16600980919743 / 20000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290814068233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_32 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82970591495751 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (143176128393 / 6250000000000 : ℝ))
      (E := (cell12396 ⟨32, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82970591495751 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (143176128393 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_33 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (2073407560283 / 2500000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290822062147 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨33, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (2073407560283 / 2500000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290822062147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_34 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82902037314091 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458165218707 / 20000000000000 : ℝ))
      (E := (cell12396 ⟨34, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82902037314091 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458165218707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_35 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41433898086447 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (143176880709 / 6250000000000 : ℝ))
      (E := (cell12396 ⟨35, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41433898086447 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (143176880709 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_36 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (20708394739179 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145417028387 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨36, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (20708394739179 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145417028387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_37 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41399692817353 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (14317737809 / 625000000000 : ℝ))
      (E := (cell12396 ⟨37, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41399692817353 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (14317737809 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_38 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (20691304044041 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290842070161 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨38, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (20691304044041 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290842070161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_39 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (82731070550551 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290846060837 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨39, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (82731070550551 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290846060837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12397_20 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83383933754337 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290633545969 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨20, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83383933754337 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290633545969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_21 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83349354656097 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (22906374921 / 1000000000000 : ℝ))
      (E := (cell12397 ⟨21, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83349354656097 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (22906374921 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_22 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (41657399965697 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (18325131879 / 800000000000 : ℝ))
      (E := (cell12397 ⟨22, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (41657399965697 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (18325131879 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_23 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (3331210781883 / 4000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290645528653 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨23, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (3331210781883 / 4000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290645528653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_24 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (41622881735079 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290649510871 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨24, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (41622881735079 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290649510871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_25 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (10401410208479 / 12500000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145326746817 / 50000000000000 : ℝ))
      (E := (cell12397 ⟨25, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (10401410208479 / 12500000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145326746817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_26 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (1299637876679 / 1562500000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290657480517 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨26, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (1299637876679 / 1562500000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290657480517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_27 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83142390756553 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (114533073743 / 5000000000000 : ℝ))
      (E := (cell12397 ⟨27, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83142390756553 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (114533073743 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_28 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (2597124424463 / 3125000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (229066547977 / 10000000000000 : ℝ))
      (E := (cell12397 ⟨28, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (2597124424463 / 3125000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (229066547977 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_29 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83073596554103 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290669498119 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨29, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83073596554103 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290669498119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_30 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (16607847127687 / 20000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458134694813 / 20000000000000 : ℝ))
      (E := (cell12397 ⟨30, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (16607847127687 / 20000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458134694813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_31 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83004898803999 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290677468453 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨31, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83004898803999 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290677468453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_32 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82970586019143 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290681483461 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨32, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82970586019143 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290681483461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_33 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82936297252377 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290685462487 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨33, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82936297252377 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290685462487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_34 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82902032472373 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290689465757 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨34, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82902032472373 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290689465757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_35 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (2071694791199 / 2500000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458138698953 / 20000000000000 : ℝ))
      (E := (cell12397 ⟨35, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (2071694791199 / 2500000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458138698953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_36 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82833574748127 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458139498431 / 20000000000000 : ℝ))
      (E := (cell12397 ⟨36, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82833574748127 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458139498431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_37 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82799381742023 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (143168841181 / 6250000000000 : ℝ))
      (E := (cell12397 ⟨37, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82799381742023 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (143168841181 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_38 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82765212598949 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145352727203 / 50000000000000 : ℝ))
      (E := (cell12397 ⟨38, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82765212598949 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145352727203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_39 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (82731067288367 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290709479277 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨39, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (82731067288367 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290709479277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12398_20 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (651436909631 / 781250000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145248482669 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨20, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (651436909631 / 781250000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145248482669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_21 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (16669869131503 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290500990387 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨21, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (16669869131503 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290500990387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_22 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41657395627673 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145252473157 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨22, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41657395627673 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145252473157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_23 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83280261193111 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290508953969 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨23, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83280261193111 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290508953969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_24 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83245755437829 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290512959129 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨24, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83245755437829 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290512959129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_25 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83211273956689 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290516965607 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨25, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83211273956689 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290516965607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_26 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (1663536334341 / 2000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145260488487 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨26, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (1663536334341 / 2000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145260488487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_27 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41571191843219 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290524938159 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨27, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41571191843219 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290524938159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_28 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41553987416273 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572632242267 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨28, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41553987416273 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572632242267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_29 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83073590123231 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (91621318229 / 4000000000000 : ℝ))
      (E := (cell12398 ⟨29, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83073590123231 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (91621318229 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_30 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41519614763259 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290536959181 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨30, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41519614763259 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290536959181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_31 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83004893010593 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (114527046167 / 5000000000000 : ℝ))
      (E := (cell12398 ⟨31, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83004893010593 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (114527046167 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_32 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (16594116108761 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145272483683 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨32, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (16594116108761 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145272483683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_33 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (16587258418933 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290548917623 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨33, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (16587258418933 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290548917623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_34 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41451013815923 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (458110590283 / 20000000000000 : ℝ))
      (E := (cell12398 ⟨34, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41451013815923 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (458110590283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_35 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (82867787124177 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (229055695311 / 10000000000000 : ℝ))
      (E := (cell12398 ⟨35, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (82867787124177 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (229055695311 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_36 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (1656671410813 / 2000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (22905609239 / 1000000000000 : ℝ))
      (E := (cell12398 ⟨36, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (1656671410813 / 2000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (22905609239 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_37 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (20699844462603 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572641230851 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨37, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (20699844462603 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572641230851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_38 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (5172825563923 / 6250000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572642238109 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨38, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (5172825563923 / 6250000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572642238109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_39 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41365532013589 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (35790202389 / 1562500000000 : ℝ))
      (E := (cell12398 ⟨39, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41365532013589 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (35790202389 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12399_20 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41691957556473 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572590124229 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨20, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41691957556473 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572590124229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_21 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (520933354129 / 625000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290364484429 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨21, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (520933354129 / 625000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290364484429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_22 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41657391290483 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290368520137 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨22, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41657391290483 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290368520137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_23 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (10410031605097 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572593122939 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨23, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (10410031605097 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572593122939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_24 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (5202859212943 / 6250000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572594129987 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨24, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (5202859212943 / 6250000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572594129987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_25 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41605633123547 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145190245931 / 50000000000000 : ℝ))
      (E := (cell12399 ⟨25, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41605633123547 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145190245931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_26 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (10397101166019 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290384469391 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨26, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (10397101166019 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290384469391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_27 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83142376617791 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290388455871 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨27, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83142376617791 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290388455871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_28 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83107968083703 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286299056801 / 12500000000000 : ℝ))
      (E := (cell12399 ⟨28, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83107968083703 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286299056801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_29 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (20768395923437 / 25000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (71574889621 / 3125000000000 : ℝ))
      (E := (cell12399 ⟨29, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (20768395923437 / 25000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (71574889621 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_30 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83039223415949 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286300062363 / 12500000000000 : ℝ))
      (E := (cell12399 ⟨30, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83039223415949 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286300062363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_31 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (16600977443699 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290404491403 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨31, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (16600977443699 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290404491403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_32 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (10371321883717 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572602111869 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨32, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (10371321883717 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572602111869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_33 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82936286938183 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572603121527 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨33, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82936286938183 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572603121527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_34 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82902022792509 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290416433359 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨34, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82902022792509 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290416433359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_35 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41433891300773 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290420466379 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨35, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41433891300773 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290420466379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_36 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (16566713266857 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145212234629 / 50000000000000 : ℝ))
      (E := (cell12399 ⟨36, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (16566713266857 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145212234629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_37 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (662394991679 / 800000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572607110741 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨37, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (662394991679 / 800000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572607110741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_38 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (4138260272381 / 5000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290432446913 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨38, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (4138260272381 / 5000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290432446913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_39 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (82731060766983 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290436423001 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨39, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (82731060766983 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290436423001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

end BstLean.Part268
