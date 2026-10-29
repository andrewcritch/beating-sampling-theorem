import BstLean.Part268CellShard1Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12375_0 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (16816207346789 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (229357305923 / 10000000000000 : ℝ))
      (E := (cell12375 ⟨0, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (16816207346789 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (229357305923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_1 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (8404595561057 / 10000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458715419001 / 20000000000000 : ℝ))
      (E := (cell12375 ⟨1, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (8404595561057 / 10000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458715419001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_2 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (84010899571791 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146790539419 / 50000000000000 : ℝ))
      (E := (cell12375 ⟨2, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (84010899571791 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (1146790539419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_3 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83975868580771 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293585078021 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨3, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83975868580771 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293585078021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_4 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83940862600873 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573397260983 / 25000000000000 : ℝ))
      (E := (cell12375 ⟨4, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83940862600873 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573397260983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_5 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (327757349983 / 390625000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (229359304339 / 10000000000000 : ℝ))
      (E := (cell12375 ⟨5, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (327757349983 / 390625000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (229359304339 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_6 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83870925528843 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293597027211 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨6, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83870925528843 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293597027211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_7 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (16767198872879 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (114680053087 / 5000000000000 : ℝ))
      (E := (cell12375 ⟨7, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (16767198872879 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (114680053087 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_8 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83801088066429 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (286700629909 / 12500000000000 : ℝ))
      (E := (cell12375 ⟨8, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83801088066429 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (286700629909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_9 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83766206599261 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293609025619 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨9, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83766206599261 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293609025619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_10 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (2616604685231 / 3125000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293613028423 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨10, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (2616604685231 / 3125000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293613028423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_11 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83696518015511 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293616997039 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨11, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83696518015511 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293616997039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_12 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83661710828489 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (143351312287 / 6250000000000 : ℝ))
      (E := (cell12375 ⟨12, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83661710828489 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (143351312287 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_13 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41813464165691 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293624975891 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨13, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41813464165691 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293624975891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_14 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (8359217048943 / 10000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293628999607 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨14, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (8359217048943 / 10000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293628999607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_15 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (83557437268051 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573408254001 / 25000000000000 : ℝ))
      (E := (cell12375 ⟨15, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (83557437268051 / 100000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573408254001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_16 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (16704545726569 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458727394601 / 20000000000000 : ℝ))
      (E := (cell12375 ⟨16, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (16704545726569 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (458727394601 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_17 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (8348804454959 / 10000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573410248179 / 25000000000000 : ℝ))
      (E := (cell12375 ⟨17, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (8348804454959 / 10000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (573410248179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_18 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (41726692492121 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293644964397 / 100000000000000 : ℝ))
      (E := (cell12375 ⟨18, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (41726692492121 / 50000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (2293644964397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12375_19 : CellCertificate 12375 (179199795569941 / 2000000000000000 : ℝ) (1697342228288629 / 1000000000000000000 : ℝ) (343075980732993 / 10000000000000000 : ℝ)
    (cell12375 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · norm_num [cell12375]
  · have h := gap_lower (n := 12375) (a := (16683749980587 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (143353059471 / 6250000000000 : ℝ))
      (E := (cell12375 ⟨19, by decide⟩).energy) (xi := (343075980732993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12375 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12375]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12375])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12375) (a := (16683749980587 / 20000000000000 : ℝ)) (b := (166503187881 / 100000000000000 : ℝ)) (q := (143353059471 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12375])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12375]

theorem cert12376_0 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (42040510399889 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (35834924799 / 1562500000000 : ℝ))
      (E := (cell12376 ⟨0, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (42040510399889 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (35834924799 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_1 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (1313217812649 / 1562500000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293439168683 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨1, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (1313217812649 / 1562500000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293439168683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_2 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (84010884303417 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146721578429 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨2, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (84010884303417 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146721578429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_3 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41987926822293 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (91737886447 / 4000000000000 : ℝ))
      (E := (cell12376 ⟨3, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41987926822293 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (91737886447 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_4 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (16788169599281 / 20000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146725566507 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨4, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (16788169599281 / 20000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146725566507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_5 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83905867322429 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (229345513919 / 10000000000000 : ℝ))
      (E := (cell12376 ⟨5, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83905867322429 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (229345513919 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_6 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (16774182317281 / 20000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146729565259 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨6, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (16774182317281 / 20000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146729565259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_7 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83835980752269 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (458692623081 / 20000000000000 : ℝ))
      (E := (cell12376 ⟨7, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83835980752269 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (458692623081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_8 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83801074784151 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146733550999 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨8, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83801074784151 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146733550999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_9 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20941548411591 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146735549097 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨9, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20941548411591 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146735549097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_10 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20932834325853 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293475111633 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨10, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20932834325853 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293475111633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_11 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (5231031607499 / 6250000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293479091669 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨11, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (5231031607499 / 6250000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293479091669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_12 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83661698860953 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293483103427 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨12, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83661698860953 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293483103427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_13 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83626916691377 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (71671471741 / 3125000000000 : ℝ))
      (E := (cell12376 ⟨13, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83626916691377 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (71671471741 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_14 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83592159176493 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (458698215019 / 20000000000000 : ℝ))
      (E := (cell12376 ⟨14, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83592159176493 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (458698215019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_15 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20889356570431 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (114674755301 / 5000000000000 : ℝ))
      (E := (cell12376 ⟨15, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20889356570431 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (114674755301 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_16 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (83522717972669 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293499078329 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨16, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (83522717972669 / 100000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293499078329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_17 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (20872008553777 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146751527977 / 50000000000000 : ℝ))
      (E := (cell12376 ⟨17, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (20872008553777 / 25000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (1146751527977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_18 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (41726687487499 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573376761119 / 25000000000000 : ℝ))
      (E := (cell12376 ⟨18, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (41726687487499 / 50000000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (573376761119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12376_19 : CellCertificate 12376 (44798480778897 / 500000000000000 : ℝ) (424301258532529 / 250000000000000000 : ℝ) (343047538269351 / 10000000000000000 : ℝ)
    (cell12376 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · norm_num [cell12376]
  · have h := gap_lower (n := 12376) (a := (10427342527309 / 12500000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293511049237 / 100000000000000 : ℝ))
      (E := (cell12376 ⟨19, by decide⟩).energy) (xi := (343047538269351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12376 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12376]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12376])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12376) (a := (10427342527309 / 12500000000000 : ℝ)) (b := (16648955911 / 10000000000000 : ℝ)) (q := (2293511049237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12376])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12376]

theorem cert12377_0 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (8408100486819 / 10000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146648654941 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨0, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (8408100486819 / 10000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146648654941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_1 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (84045924411039 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293301295043 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨1, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (84045924411039 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293301295043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_2 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (42005434518769 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146652643813 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨2, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (42005434518769 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146652643813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_3 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41987919355427 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (458661859429 / 20000000000000 : ℝ))
      (E := (cell12377 ⟨3, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41987919355427 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (458661859429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_4 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (1678816667887 / 2000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293313274977 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨4, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (1678816667887 / 2000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293313274977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_5 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41952926525791 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (139972979 / 6103515625 : ℝ))
      (E := (cell12377 ⟨5, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41952926525791 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (139972979 / 6103515625 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_6 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (10483862205787 / 12500000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293321286839 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨6, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (10483862205787 / 12500000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293321286839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_7 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83835967142433 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293325280087 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨7, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83835967142433 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293325280087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_8 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83801061504119 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293329275833 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨8, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83801061504119 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293329275833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_9 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83766180695673 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146666640983 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨9, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83766180695673 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146666640983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_10 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83731324681597 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146668624059 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨10, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83731324681597 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146668624059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_11 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83696493426581 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293341239641 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨11, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83696493426581 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293341239641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_12 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83661686895501 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573336315917 / 25000000000000 : ℝ))
      (E := (cell12377 ⟨12, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83661686895501 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (573336315917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_13 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83626905053413 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293349269007 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨13, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83626905053413 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293349269007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_14 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41796073932779 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (91734130489 / 4000000000000 : ℝ))
      (E := (cell12377 ⟨14, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41796073932779 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (91734130489 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_15 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41778707648679 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146678624819 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨15, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41778707648679 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146678624819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_16 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41761353657207 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293361237321 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨16, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41761353657207 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293361237321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_17 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (41744011941253 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293365231099 / 100000000000000 : ℝ))
      (E := (cell12377 ⟨17, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (41744011941253 / 50000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (2293365231099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_18 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (10431670620949 / 12500000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146684618277 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨18, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (10431670620949 / 12500000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146684618277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12377_19 : CellCertificate 12377 (89594025787353 / 1000000000000000 : ℝ) (1697067862148291 / 1000000000000000000 : ℝ) (42877387578031 / 1250000000000000 : ℝ)
    (cell12377 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · norm_num [cell12377]
  · have h := gap_lower (n := 12377) (a := (83418730535807 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146686600401 / 50000000000000 : ℝ))
      (E := (cell12377 ⟨19, by decide⟩).energy) (xi := (42877387578031 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12377 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12377]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12377])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12377) (a := (83418730535807 / 100000000000000 : ℝ)) (b := (41618983149 / 25000000000000 : ℝ)) (q := (1146686600401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12377])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12377]

theorem cert12378_0 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (84080988939179 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (91726381721 / 4000000000000 : ℝ))
      (E := (cell12378 ⟨0, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (84080988939179 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (91726381721 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_1 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (42022954407539 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (143322720743 / 6250000000000 : ℝ))
      (E := (cell12378 ⟨1, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (42022954407539 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (143322720743 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_2 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (42005426887077 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (229316752897 / 10000000000000 : ℝ))
      (E := (cell12378 ⟨2, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (42005426887077 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (229316752897 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_3 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (10496977972447 / 12500000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146585771889 / 50000000000000 : ℝ))
      (E := (cell12378 ⟨3, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (10496977972447 / 12500000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (1146585771889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_4 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83940818794707 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293175527693 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨4, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83940818794707 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293175527693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_5 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (655514365493 / 781250000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293179489633 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨5, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (655514365493 / 781250000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293179489633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_6 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83870883708517 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (91727339847 / 4000000000000 : ℝ))
      (E := (cell12378 ⟨6, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83870883708517 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (91727339847 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_7 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (20958988383721 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293187497853 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨7, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (20958988383721 / 25000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293187497853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_8 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (41900524113167 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458638300563 / 20000000000000 : ℝ))
      (E := (cell12378 ⟨8, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (41900524113167 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458638300563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_9 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83766167747187 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (286649439869 / 12500000000000 : ℝ))
      (E := (cell12378 ⟨9, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83766167747187 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (286649439869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_10 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (41865656030973 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293199495893 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨10, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (41865656030973 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293199495893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_11 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (41848240567651 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (229320349899 / 10000000000000 : ℝ))
      (E := (cell12378 ⟨11, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (41848240567651 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (229320349899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_12 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83661674932131 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293207477319 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨12, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83661674932131 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293207477319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_13 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83626893417491 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293211495777 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨13, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83626893417491 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293211495777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_14 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (5224508534789 / 6250000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (229321544479 / 10000000000000 : ℝ))
      (E := (cell12378 ⟨14, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (5224508534789 / 6250000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (229321544479 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_15 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (10444675539369 / 12500000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293219446863 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨15, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (10444675539369 / 12500000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293219446863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_16 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (41761348329039 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (17915808203 / 781250000000 : ℝ))
      (E := (cell12378 ⟨16, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (41761348329039 / 50000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (17915808203 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_17 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (83488013551783 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (114661372999 / 5000000000000 : ℝ))
      (E := (cell12378 ⟨17, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (83488013551783 / 100000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (114661372999 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_18 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (3338134198481 / 4000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293231424233 / 100000000000000 : ℝ))
      (E := (cell12378 ⟨18, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (3338134198481 / 4000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (2293231424233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12378_19 : CellCertificate 12378 (447955452367679 / 5000000000000000 : ℝ) (1696930712337777 / 1000000000000000000 : ℝ) (171495333898157 / 5000000000000000 : ℝ)
    (cell12378 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · norm_num [cell12378]
  · have h := gap_lower (n := 12378) (a := (4170936042747 / 5000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458647092891 / 20000000000000 : ℝ))
      (E := (cell12378 ⟨19, by decide⟩).energy) (xi := (171495333898157 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12378 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12378]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12378])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12378) (a := (4170936042747 / 5000000000000 : ℝ)) (b := (166462308337 / 100000000000000 : ℝ)) (q := (458647092891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12378])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12378]

theorem cert12379_0 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (16816194602549 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293021828789 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨0, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (16816194602549 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293021828789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_1 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (21011473305413 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146512910711 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨1, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (21011473305413 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146512910711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_2 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (84010838513263 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293029823067 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨2, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (84010838513263 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293029823067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_3 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83975808850749 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146516892693 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨3, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83975808850749 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146516892693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_4 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41970402098737 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146518887713 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨4, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41970402098737 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146518887713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_5 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (20976456129249 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (91721672087 / 4000000000000 : ℝ))
      (E := (cell12379 ⟨5, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (20976456129249 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (91721672087 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_6 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (16774173954613 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146522908223 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨6, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (16774173954613 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146522908223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_7 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41917969964811 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293049768701 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨7, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41917969964811 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293049768701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_8 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (20950258737699 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458610756589 / 20000000000000 : ℝ))
      (E := (cell12379 ⟨8, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (20950258737699 / 25000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458610756589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_9 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41883077400453 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (573264437791 / 25000000000000 : ℝ))
      (E := (cell12379 ⟨9, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41883077400453 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (573264437791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_10 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83731299444459 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293061796949 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨10, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83731299444459 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293061796949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_11 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41848234423073 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293065753651 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨11, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41848234423073 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293065753651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_12 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83661662970843 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293069744381 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨12, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83661662970843 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293069744381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_13 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (8362688178361 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293073776023 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨13, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (8362688178361 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293073776023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_14 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (8359212524969 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146538869501 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨14, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (8359212524969 / 10000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146538869501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_15 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41778696667253 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146540877911 / 50000000000000 : ℝ))
      (E := (cell12379 ⟨15, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41778696667253 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (1146540877911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_16 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83522686003661 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (14331785727 / 625000000000 : ℝ))
      (E := (cell12379 ⟨16, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83522686003661 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (14331785727 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_17 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (41744001611469 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293089742599 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨17, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (41744001611469 / 50000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293089742599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_18 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (16690668991659 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458618744783 / 20000000000000 : ℝ))
      (E := (cell12379 ⟨18, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (16690668991659 / 20000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (458618744783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12379_19 : CellCertificate 12379 (89588155616231 / 1000000000000000 : ℝ) (848396792346599 / 500000000000000000 : ℝ) (21435139986511 / 625000000000000 : ℝ)
    (cell12379 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · norm_num [cell12379]
  · have h := gap_lower (n := 12379) (a := (83418711175871 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293097723753 / 100000000000000 : ℝ))
      (E := (cell12379 ⟨19, by decide⟩).energy) (xi := (21435139986511 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12379 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12379]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12379])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12379) (a := (83418711175871 / 100000000000000 : ℝ)) (b := (166448686333 / 100000000000000 : ℝ)) (q := (2293097723753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12379])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12379]

theorem cert12380_0 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (10510119636111 / 12500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (91715366687 / 4000000000000 : ℝ))
      (E := (cell12380 ⟨0, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (10510119636111 / 12500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (91715366687 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_1 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (2101146940769 / 2500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458577632729 / 20000000000000 : ℝ))
      (E := (cell12380 ⟨1, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (2101146940769 / 2500000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458577632729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_2 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (42005411627433 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292892169919 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨2, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (42005411627433 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292892169919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_3 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (134361270279 / 160000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (114644806883 / 5000000000000 : ℝ))
      (E := (cell12380 ⟨3, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (134361270279 / 160000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (114644806883 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_4 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (20985197400663 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458580026783 / 20000000000000 : ℝ))
      (E := (cell12380 ⟨4, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (20985197400663 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458580026783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_5 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41952905126629 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292904167669 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨5, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41952905126629 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292904167669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_6 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41935427919971 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146454065909 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨6, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41935427919971 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146454065909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_7 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41917963163323 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (91716486023 / 4000000000000 : ℝ))
      (E := (cell12380 ⟨7, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41917963163323 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (91716486023 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_8 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41900510838751 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146458058113 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨8, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41900510838751 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146458058113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_9 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83766141856829 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292920094581 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨9, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83766141856829 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292920094581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_10 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (16746257365827 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (91716963731 / 4000000000000 : ℝ))
      (E := (cell12380 ⟨10, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (16746257365827 / 20000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (91716963731 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_11 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83696456559111 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458585623939 / 20000000000000 : ℝ))
      (E := (cell12380 ⟨11, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83696456559111 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (458585623939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_12 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (20915412752909 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146466061457 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨12, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (20915412752909 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146466061457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_13 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (8362687015177 / 10000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292936109747 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨13, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (8362687015177 / 10000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292936109747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_14 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (20898028486189 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146470043379 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨14, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (20898028486189 / 25000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146470043379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_15 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83557382356019 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146472030131 / 50000000000000 : ℝ))
      (E := (cell12380 ⟨15, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83557382356019 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (1146472030131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_16 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83522675351163 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (28661851181 / 1250000000000 : ℝ))
      (E := (cell12380 ⟨16, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83522675351163 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (28661851181 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_17 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83487992895971 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292952078957 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨17, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83487992895971 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292952078957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_18 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (83453334956403 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (11464780387 / 500000000000 : ℝ))
      (E := (cell12380 ⟨18, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (83453334956403 / 100000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (11464780387 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12380_19 : CellCertificate 12380 (895852212153269 / 10000000000000000 : ℝ) (1696656479209183 / 1000000000000000000 : ℝ) (342933816586467 / 10000000000000000 : ℝ)
    (cell12380 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · norm_num [cell12380]
  · have h := gap_lower (n := 12380) (a := (41709350749299 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292960095143 / 100000000000000 : ℝ))
      (E := (cell12380 ⟨19, by decide⟩).energy) (xi := (342933816586467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12380 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12380]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12380])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12380) (a := (41709350749299 / 50000000000000 : ℝ)) (b := (166435066583 / 100000000000000 : ℝ)) (q := (2292960095143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12380])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12380]

theorem cert12381_0 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (42040470583803 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146373279093 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨0, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (42040470583803 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146373279093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_1 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (84045862042403 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146375279279 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨1, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (84045862042403 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146375279279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_2 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (84010807998961 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (286594321191 / 12500000000000 : ℝ))
      (E := (cell12381 ⟨2, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (84010807998961 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (286594321191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_3 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83975779000451 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146379271379 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨3, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83975779000451 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146379271379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_4 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (262314921907 / 312500000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (573190636323 / 25000000000000 : ℝ))
      (E := (cell12381 ⟨4, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (262314921907 / 312500000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (573190636323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_5 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83905795991887 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (71648954007 / 3125000000000 : ℝ))
      (E := (cell12381 ⟨5, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83905795991887 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (71648954007 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_6 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (16774168381829 / 20000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (143298159883 / 6250000000000 : ℝ))
      (E := (cell12381 ⟨6, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (16774168381829 / 20000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (143298159883 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_7 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83835912725957 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292774527593 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨7, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83835912725957 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292774527593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_8 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83801008406453 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292778560623 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨8, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83801008406453 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292778560623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_9 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83766128914957 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292782549201 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨9, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83766128914957 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292782549201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_10 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (41865637107987 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458557300179 / 20000000000000 : ℝ))
      (E := (cell12381 ⟨10, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (41865637107987 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458557300179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_11 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83696444274199 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146395269543 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨11, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83696444274199 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146395269543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_12 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (8366163905451 / 10000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292794496803 / 100000000000000 : ℝ))
      (E := (cell12381 ⟨12, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (8366163905451 / 10000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (2292794496803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_13 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (8362685852197 / 10000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (45855969939 / 2000000000000 : ℝ))
      (E := (cell12381 ⟨13, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (8362685852197 / 10000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (45855969939 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_14 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83592102641821 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146401244029 / 50000000000000 : ℝ))
      (E := (cell12381 ⟨14, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83592102641821 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (1146401244029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_15 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (8355737137949 / 10000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (57320161911 / 2500000000000 : ℝ))
      (E := (cell12381 ⟨15, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (8355737137949 / 10000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (57320161911 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_16 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (41761332350291 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458562093633 / 20000000000000 : ℝ))
      (E := (cell12381 ⟨16, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (41761332350291 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458562093633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_17 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (83487982570881 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458562893811 / 20000000000000 : ℝ))
      (E := (cell12381 ⟨17, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (83487982570881 / 100000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (458562893811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_18 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (20863331239087 / 25000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (229281848469 / 10000000000000 : ℝ))
      (E := (cell12381 ⟨18, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (20863331239087 / 25000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (229281848469 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12381_19 : CellCertificate 12381 (895822872707121 / 10000000000000000 : ℝ) (848259697940179 / 500000000000000000 : ℝ) (68581079640363 / 2000000000000000 : ℝ)
    (cell12381 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · norm_num [cell12381]
  · have h := gap_lower (n := 12381) (a := (41709345911561 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (114641123109 / 5000000000000 : ℝ))
      (E := (cell12381 ⟨19, by decide⟩).energy) (xi := (68581079640363 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12381 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12381]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12381])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12381) (a := (41709345911561 / 50000000000000 : ℝ)) (b := (166421449087 / 100000000000000 : ℝ)) (q := (114641123109 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12381])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12381]

theorem cert12382_0 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (84080925248899 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292609059599 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨0, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (84080925248899 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292609059599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_1 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (84045846456579 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292613063963 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨1, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (84045846456579 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292613063963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_2 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (21002698186387 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458523404379 / 20000000000000 : ℝ))
      (E := (cell12382 ⟨2, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (21002698186387 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458523404379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_3 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41987882039489 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292621058527 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨3, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41987882039489 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292621058527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_4 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83940760420237 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (57315625239 / 2500000000000 : ℝ))
      (E := (cell12382 ⟨4, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83940760420237 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (57315625239 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_5 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16781156346577 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292628999629 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨5, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16781156346577 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292628999629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_6 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (20967706995169 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292633037459 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨6, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (20967706995169 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292633037459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_7 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83835899127553 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (57315925391 / 2500000000000 : ℝ))
      (E := (cell12382 ⟨7, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83835899127553 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (57315925391 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_8 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83800995137649 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292641000209 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨8, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83800995137649 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292641000209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_9 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83766115975287 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146322499527 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨9, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83766115975287 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146322499527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_10 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (3349250464199 / 4000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (229264901981 / 10000000000000 : ℝ))
      (E := (cell12382 ⟨10, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (3349250464199 / 4000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (229264901981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_11 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (5231026999463 / 6250000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292653011827 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨11, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (5231026999463 / 6250000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292653011827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_12 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16732325419893 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458531396433 / 20000000000000 : ℝ))
      (E := (cell12382 ⟨12, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16732325419893 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (458531396433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_13 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83626846894209 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (573165248929 / 25000000000000 : ℝ))
      (E := (cell12382 ⟨13, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83626846894209 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (573165248929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_14 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (16718418268177 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (229266500101 / 10000000000000 : ℝ))
      (E := (cell12382 ⟨14, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (16718418268177 / 20000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (229266500101 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_15 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (2088934010123 / 2500000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292668946229 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨15, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (2088934010123 / 2500000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292668946229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_16 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83522654051919 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146336476839 / 50000000000000 : ℝ))
      (E := (cell12382 ⟨16, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83522654051919 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1146336476839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_17 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (20871993061917 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292676971071 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨17, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (20871993061917 / 25000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292676971071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_18 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (83453314958129 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292680945787 / 100000000000000 : ℝ))
      (E := (cell12382 ⟨18, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (83453314958129 / 100000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (2292680945787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12382_19 : CellCertificate 12382 (3583174151291 / 40000000000000 : ℝ) (339276466940271 / 200000000000000000 : ℝ) (171438492314427 / 5000000000000000 : ℝ)
    (cell12382 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · norm_num [cell12382]
  · have h := gap_lower (n := 12382) (a := (41709341074721 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1119475069 / 48828125000 : ℝ))
      (E := (cell12382 ⟨19, by decide⟩).energy) (xi := (171438492314427 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12382 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12382]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12382])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12382) (a := (41709341074721 / 50000000000000 : ℝ)) (b := (41601958461 / 25000000000000 : ℝ)) (q := (1119475069 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12382])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12382]

theorem cert12383_0 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (84080909332767 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (57311790341 / 2500000000000 : ℝ))
      (E := (cell12383 ⟨0, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (84080909332767 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (57311790341 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_1 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (84045830873289 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292475564261 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨1, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (84045830873289 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292475564261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_2 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (84010777494627 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146239792423 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨2, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (84010777494627 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146239792423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_3 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (16795149831991 / 20000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146241784637 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨3, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (16795149831991 / 20000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146241784637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_4 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41970372916321 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292487584591 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨4, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41970372916321 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292487584591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_5 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (67124613981 / 80000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146245790943 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨5, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (67124613981 / 80000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146245790943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_6 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (20967703513633 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458499113963 / 20000000000000 : ℝ))
      (E := (cell12383 ⟨6, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (20967703513633 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (458499113963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_7 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83835885531433 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292499556777 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨7, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83835885531433 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292499556777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_8 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83800981871089 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292503550913 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨8, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83800981871089 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292503550913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_9 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (4188305151891 / 5000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146253780057 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨9, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (4188305151891 / 5000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146253780057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_10 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41865624498069 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292511534001 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨10, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41865624498069 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292511534001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_11 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41848209855369 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (447756941 / 19531250000 : ℝ))
      (E := (cell12383 ⟨11, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41848209855369 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (447756941 / 19531250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_12 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (167323230293 / 200000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (143282470059 / 6250000000000 : ℝ))
      (E := (cell12383 ⟨12, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (167323230293 / 200000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (143282470059 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_13 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (10453354408561 / 12500000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292523489883 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨13, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (10453354408561 / 12500000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292523489883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_14 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (20898020010487 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292527509403 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨14, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (20898020010487 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292527509403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_15 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83557349432307 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292531527761 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨15, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83557349432307 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292531527761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_16 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83522643405173 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292535492869 / 100000000000000 : ℝ))
      (E := (cell12383 ⟨16, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83522643405173 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (2292535492869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_17 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (20871990481583 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146269734327 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨17, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (20871990481583 / 25000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146269734327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_18 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (41726652480873 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (573135879723 / 25000000000000 : ℝ))
      (E := (cell12383 ⟨18, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (41726652480873 / 50000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (573135879723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12383_19 : CellCertificate 12383 (895764207499043 / 10000000000000000 : ℝ) (339249059133361 / 200000000000000000 : ℝ) (171424287933107 / 5000000000000000 : ℝ)
    (cell12383 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · norm_num [cell12383]
  · have h := gap_lower (n := 12383) (a := (83418672477557 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146273737159 / 50000000000000 : ℝ))
      (E := (cell12383 ⟨19, by decide⟩).energy) (xi := (171424287933107 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12383 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12383]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12383])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12383) (a := (83418672477557 / 100000000000000 : ℝ)) (b := (166394220853 / 100000000000000 : ℝ)) (q := (1146273737159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12383])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12383]

theorem cert12384_0 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (10510111677401 / 12500000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146167081267 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨0, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (10510111677401 / 12500000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146167081267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_1 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (8404581529253 / 10000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143271135941 / 6250000000000 : ℝ))
      (E := (cell12384 ⟨1, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (8404581529253 / 10000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (143271135941 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_2 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (21002690561549 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146171100279 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨2, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (21002690561549 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146171100279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_3 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41987867121691 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286543273837 / 12500000000000 : ℝ))
      (E := (cell12384 ⟨3, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41987867121691 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286543273837 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_4 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (2623147851483 / 3125000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292350154643 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨4, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (2623147851483 / 3125000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292350154643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_5 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83905753221981 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286544269901 / 12500000000000 : ℝ))
      (E := (cell12384 ⟨5, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83905753221981 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286544269901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_6 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41935400065357 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458471631039 / 20000000000000 : ℝ))
      (E := (cell12384 ⟨6, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41935400065357 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458471631039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_7 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83835871937599 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292362151003 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨7, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83835871937599 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292362151003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_8 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83800968606771 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286545769347 / 12500000000000 : ℝ))
      (E := (cell12384 ⟨8, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83800968606771 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286545769347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_9 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (20941522525639 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286546264551 / 12500000000000 : ℝ))
      (E := (cell12384 ⟨9, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (20941522525639 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (286546264551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_10 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41865618194731 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (229237415949 / 10000000000000 : ℝ))
      (E := (cell12384 ⟨10, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41865618194731 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (229237415949 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_11 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (20924101858047 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458475623473 / 20000000000000 : ℝ))
      (E := (cell12384 ⟨11, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (20924101858047 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458475623473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_12 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (41830801597807 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292382113141 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨12, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (41830801597807 / 50000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292382113141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_13 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (16725364728961 / 20000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458477219123 / 20000000000000 : ℝ))
      (E := (cell12384 ⟨13, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (16725364728961 / 20000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (458477219123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_14 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (5224504296563 / 6250000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (573097532363 / 25000000000000 : ℝ))
      (E := (cell12384 ⟨14, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (5224504296563 / 6250000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (573097532363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_15 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (20889334615413 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292394104777 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨15, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (20889334615413 / 25000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292394104777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_16 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (10440329095043 / 12500000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292398085739 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨16, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (10440329095043 / 12500000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292398085739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_17 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83487951606871 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146201039079 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨17, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83487951606871 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146201039079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_18 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83453294967199 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292406087607 / 100000000000000 : ℝ))
      (E := (cell12384 ⟨18, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83453294967199 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (2292406087607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12384_19 : CellCertificate 12384 (179146976346977 / 2000000000000000 : ℝ) (848054139385671 / 500000000000000000 : ℝ) (34282017191253 / 1000000000000000 : ℝ)
    (cell12384 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · norm_num [cell12384]
  · have h := gap_lower (n := 12384) (a := (83418662807467 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146205030599 / 50000000000000 : ℝ))
      (E := (cell12384 ⟨19, by decide⟩).energy) (xi := (34282017191253 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12384 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12384]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12384])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12384) (a := (83418662807467 / 100000000000000 : ℝ)) (b := (83190305057 / 50000000000000 : ℝ)) (q := (1146205030599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12384])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12384]

theorem cert12385_0 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (84080877508223 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146098410917 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨0, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (84080877508223 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146098410917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_1 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (84045799714303 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146100419273 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨1, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (84045799714303 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146100419273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_2 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (1312667921879 / 1562500000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (286525601401 / 12500000000000 : ℝ))
      (E := (cell12385 ⟨2, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (1312667921879 / 1562500000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (286525601401 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_3 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83975719329257 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292208807099 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨3, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83975719329257 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292208807099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_4 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83940716664677 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292212835461 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨4, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83940716664677 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292212835461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_5 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83905738970079 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (286527105923 / 12500000000000 : ℝ))
      (E := (cell12385 ⟨5, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83905738970079 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (286527105923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_6 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (4193539310461 / 5000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292220793601 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨6, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (4193539310461 / 5000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292220793601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_7 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83835858346047 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292224798323 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨7, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83835858346047 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292224798323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_8 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83800955344697 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146114405897 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨8, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83800955344697 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146114405897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_9 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (20941519292373 / 25000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458446556783 / 20000000000000 : ℝ))
      (E := (cell12385 ⟨9, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (20941519292373 / 25000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458446556783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_10 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83731223784947 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (71632399383 / 3125000000000 : ℝ))
      (E := (cell12385 ⟨10, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83731223784947 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (71632399383 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_11 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83696395155757 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292240808201 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨11, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83696395155757 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292240808201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_12 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41830795623403 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292244758759 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨12, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41830795623403 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292244758759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_13 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (2090670300579 / 2500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (143265547177 / 6250000000000 : ℝ))
      (E := (cell12385 ⟨13, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (2090670300579 / 2500000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (143265547177 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_14 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41796028725033 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458450548989 / 20000000000000 : ℝ))
      (E := (cell12385 ⟨14, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41796028725033 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (458450548989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_15 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (83557327492953 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146128396769 / 50000000000000 : ℝ))
      (E := (cell12385 ⟨15, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (83557327492953 / 100000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (1146128396769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_16 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (8352262211743 / 10000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292260790443 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨16, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (8352262211743 / 10000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292260790443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_17 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41743970644643 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292264741407 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨17, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41743970644643 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292264741407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_18 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (41726642487243 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292268768333 / 100000000000000 : ℝ))
      (E := (cell12385 ⟨18, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (41726642487243 / 50000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (2292268768333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12385_19 : CellCertificate 12385 (447852780264581 / 5000000000000000 : ℝ) (847985642004801 / 500000000000000000 : ℝ) (171395886383217 / 5000000000000000 : ℝ)
    (cell12385 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · norm_num [cell12385]
  · have h := gap_lower (n := 12385) (a := (20854663284793 / 25000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (143267047511 / 6250000000000 : ℝ))
      (E := (cell12385 ⟨19, by decide⟩).energy) (xi := (171395886383217 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12385 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12385]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12385])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12385) (a := (20854663284793 / 25000000000000 : ℝ)) (b := (166367001627 / 100000000000000 : ℝ)) (q := (143267047511 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12385])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12385]

theorem cert12386_0 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (8408086159981 / 10000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292059591543 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨0, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (8408086159981 / 10000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292059591543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_1 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (5252861508663 / 6250000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146031777367 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨1, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (5252861508663 / 6250000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146031777367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_2 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (16802146351361 / 20000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146033766223 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨2, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (16802146351361 / 20000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146033766223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_3 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (4198785220879 / 5000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292071534179 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨3, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (4198785220879 / 5000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292071534179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_4 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (5246293880269 / 6250000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286509446147 / 12500000000000 : ℝ))
      (E := (cell12386 ⟨4, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (5246293880269 / 6250000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286509446147 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_5 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41952862360271 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292079530627 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨5, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41952862360271 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292079530627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_6 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83870772290051 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286510442869 / 12500000000000 : ℝ))
      (E := (cell12386 ⟨6, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83870772290051 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (286510442869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_7 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83835844756779 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573021889169 / 25000000000000 : ℝ))
      (E := (cell12386 ⟨7, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83835844756779 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573021889169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_8 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (327347430019 / 390625000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573022880493 / 25000000000000 : ℝ))
      (E := (cell12386 ⟨8, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (327347430019 / 390625000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573022880493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_9 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (8376606423863 / 10000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458419100929 / 20000000000000 : ℝ))
      (E := (cell12386 ⟨9, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (8376606423863 / 10000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458419100929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_10 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83731211182591 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (91683980493 / 4000000000000 : ℝ))
      (E := (cell12386 ⟨10, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83731211182591 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (91683980493 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_11 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41848191440723 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573025873589 / 25000000000000 : ℝ))
      (E := (cell12386 ⟨11, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41848191440723 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573025873589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_12 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (41830789650039 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146053757927 / 50000000000000 : ℝ))
      (E := (cell12386 ⟨12, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (41830789650039 / 50000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (1146053757927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_13 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (2613337512611 / 3125000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292111525617 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨13, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (2613337512611 / 3125000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292111525617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_14 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (261225144241 / 312500000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458423094419 / 20000000000000 : ℝ))
      (E := (cell12386 ⟨14, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (261225144241 / 312500000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (458423094419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_15 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (8355731652621 / 10000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292119477787 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨15, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (8355731652621 / 10000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292119477787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_16 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (5220163217277 / 6250000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573030872669 / 25000000000000 : ℝ))
      (E := (cell12386 ⟨16, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (5220163217277 / 6250000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (573030872669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_17 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (10435991371697 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292127458403 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨17, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (10435991371697 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292127458403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_18 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (10431659372951 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (229213150287 / 10000000000000 : ℝ))
      (E := (cell12386 ⟨18, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (10431659372951 / 12500000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (229213150287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12386_19 : CellCertificate 12386 (895676243880761 / 10000000000000000 : ℝ) (847917155688111 / 500000000000000000 : ℝ) (342763378426561 / 10000000000000000 : ℝ)
    (cell12386 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · norm_num [cell12386]
  · have h := gap_lower (n := 12386) (a := (83418643472671 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292135454809 / 100000000000000 : ℝ))
      (E := (cell12386 ⟨19, by decide⟩).energy) (xi := (342763378426561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12386 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12386]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12386])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12386) (a := (83418643472671 / 100000000000000 : ℝ)) (b := (166353395391 / 100000000000000 : ℝ)) (q := (2292135454809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12386])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12386]

theorem cert12387_0 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (8408084569397 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (229192235611 / 10000000000000 : ℝ))
      (E := (cell12387 ⟨0, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (8408084569397 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (229192235611 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_1 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (42022884282721 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (91677055257 / 4000000000000 : ℝ))
      (E := (cell12387 ⟨1, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (42022884282721 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (91677055257 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_2 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (21002679128961 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145965182137 / 50000000000000 : ℝ))
      (E := (cell12387 ⟨2, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (21002679128961 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145965182137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_3 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83975689508351 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (572983578523 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨3, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83975689508351 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (572983578523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_4 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41970343753169 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (572984588947 / 25000000000000 : ℝ))
      (E := (cell12387 ⟨4, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41970343753169 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (572984588947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_5 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83905710473371 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2291942324729 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨5, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83905710473371 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2291942324729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_6 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41935379186603 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145973172667 / 50000000000000 : ℝ))
      (E := (cell12387 ⟨6, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41935379186603 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145973172667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_7 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41917915584897 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (286493788773 / 12500000000000 : ℝ))
      (E := (cell12387 ⟨7, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41917915584897 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (286493788773 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_8 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83800928827273 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2291954285311 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨8, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83800928827273 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2291954285311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_9 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83766051309969 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145979139301 / 50000000000000 : ℝ))
      (E := (cell12387 ⟨9, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83766051309969 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145979139301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_10 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (20932799645599 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458392459537 / 20000000000000 : ℝ))
      (E := (cell12387 ⟨10, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (20932799645599 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458392459537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_11 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41848185304627 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (35811973311 / 1562500000000 : ℝ))
      (E := (cell12387 ⟨11, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41848185304627 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (35811973311 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_12 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41830783677713 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2291970268317 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨12, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41830783677713 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2291970268317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_13 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (41813394392991 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2291974291809 / 100000000000000 : ℝ))
      (E := (cell12387 ⟨13, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (41813394392991 / 50000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (2291974291809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_14 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (8359203486617 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (179060801 / 7812500000 : ℝ))
      (E := (cell12387 ⟨14, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (8359203486617 / 10000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (179060801 / 7812500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_15 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83557305561423 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458396454757 / 20000000000000 : ℝ))
      (E := (cell12387 ⟨15, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83557305561423 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458396454757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_16 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83522600837349 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145993122297 / 50000000000000 : ℝ))
      (E := (cell12387 ⟨16, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83522600837349 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145993122297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_17 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83487920659741 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (91679611493 / 4000000000000 : ℝ))
      (E := (cell12387 ⟨17, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83487920659741 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (91679611493 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_18 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (20863316248641 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145997145611 / 50000000000000 : ℝ))
      (E := (cell12387 ⟨18, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (20863316248641 / 25000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (1145997145611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12387_19 : CellCertificate 12387 (89564693178857 / 1000000000000000 : ℝ) (1695697360865841 / 1000000000000000000 : ℝ) (68546997778309 / 2000000000000000 : ℝ)
    (cell12387 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · norm_num [cell12387]
  · have h := gap_lower (n := 12387) (a := (83418633807963 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458399652309 / 20000000000000 : ℝ))
      (E := (cell12387 ⟨19, by decide⟩).energy) (xi := (68546997778309 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12387 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12387]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12387])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12387) (a := (83418633807963 / 100000000000000 : ℝ)) (b := (41584947851 / 25000000000000 : ℝ)) (q := (458399652309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12387])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12387]

theorem cert12388_0 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (840808297907 / 1000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291785231089 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨0, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (840808297907 / 1000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291785231089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_1 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (84045752994807 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145894601507 / 50000000000000 : ℝ))
      (E := (cell12388 ⟨1, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (84045752994807 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145894601507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_2 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (8401070127737 / 10000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291793191047 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨2, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (8401070127737 / 10000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291793191047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_3 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83975674601569 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145898602343 / 50000000000000 : ℝ))
      (E := (cell12388 ⟨3, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83975674601569 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (1145898602343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_4 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41970336465389 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (22918011953 / 1000000000000 : ℝ))
      (E := (cell12388 ⟨4, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41970336465389 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (22918011953 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_5 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83905696228563 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291805171797 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨5, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83905696228563 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291805171797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_6 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (20967686114671 / 25000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572952285707 / 25000000000000 : ℝ))
      (E := (cell12388 ⟨6, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (20967686114671 / 25000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572952285707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_7 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83835817585091 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291813174729 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨7, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83835817585091 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291813174729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_8 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83800915571923 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291817159777 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨8, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83800915571923 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291817159777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_9 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83766038383507 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (91672846551 / 4000000000000 : ℝ))
      (E := (cell12388 ⟨9, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83766038383507 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (91672846551 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_10 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83731185984359 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291825136339 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨10, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83731185984359 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291825136339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_11 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83696358339179 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572957285703 / 25000000000000 : ℝ))
      (E := (cell12388 ⟨11, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83696358339179 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572957285703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_12 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83661555412853 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (114591656613 / 5000000000000 : ℝ))
      (E := (cell12388 ⟨12, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83661555412853 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (114591656613 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_13 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (5226673573153 / 6250000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291837111491 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨13, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (5226673573153 / 6250000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291837111491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_14 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83592023577217 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572960286291 / 25000000000000 : ℝ))
      (E := (cell12388 ⟨14, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83592023577217 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (572960286291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_15 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (8355729459859 / 10000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291845123403 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨15, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (8355729459859 / 10000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291845123403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_16 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83522590200181 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291849110349 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨16, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83522590200181 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291849110349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_17 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83487910347779 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291853111821 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨17, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83487910347779 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291853111821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_18 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (41726627503677 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291857133389 / 100000000000000 : ℝ))
      (E := (cell12388 ⟨18, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (41726627503677 / 50000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (2291857133389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12388_19 : CellCertificate 12388 (35824704970059 / 400000000000000 : ℝ) (1695560432473099 / 1000000000000000000 : ℝ) (342706604160023 / 10000000000000000 : ℝ)
    (cell12388 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · norm_num [cell12388]
  · have h := gap_lower (n := 12388) (a := (83418624145049 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (28648264027 / 1250000000000 : ℝ))
      (E := (cell12388 ⟨19, by decide⟩).energy) (xi := (342706604160023 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12388 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12388]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12388])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12388) (a := (83418624145049 / 100000000000000 : ℝ)) (b := (166326189667 / 100000000000000 : ℝ)) (q := (28648264027 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12388])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12388]

theorem cert12389_0 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (42040406945001 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (35807001577 / 1562500000000 : ℝ))
      (E := (cell12389 ⟨0, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (42040406945001 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (35807001577 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_1 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (84045737426701 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572913033777 / 25000000000000 : ℝ))
      (E := (cell12389 ⟨1, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (84045737426701 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572913033777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_2 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16802137208277 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572914032103 / 25000000000000 : ℝ))
      (E := (cell12389 ⟨2, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16802137208277 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572914032103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_3 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41987829848617 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291660090267 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨3, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41987829848617 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291660090267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_4 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83940658357623 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (71614502741 / 3125000000000 : ℝ))
      (E := (cell12389 ⟨4, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83940658357623 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (71614502741 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_5 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (2097642049653 / 2500000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (229166807183 / 10000000000000 : ℝ))
      (E := (cell12389 ⟨5, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (2097642049653 / 2500000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (229166807183 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_6 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16774146109297 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291672109191 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨6, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16774146109297 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291672109191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_7 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83835804002669 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291676092373 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨7, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83835804002669 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291676092373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_8 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83800902318813 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (143230005463 / 6250000000000 : ℝ))
      (E := (cell12389 ⟨8, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83800902318813 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (143230005463 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_9 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16753205091849 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291684044189 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨9, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16753205091849 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291684044189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_10 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83731173388481 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (22916880863 / 1000000000000 : ℝ))
      (E := (cell12389 ⟨10, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83731173388481 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (22916880863 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_11 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41848173035611 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (57292301177 / 2500000000000 : ℝ))
      (E := (cell12389 ⟨11, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41848173035611 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (57292301177 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_12 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (16732308694471 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291696049631 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨12, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (16732308694471 / 20000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291696049631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_13 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (1672535311139 / 2000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145850021373 / 50000000000000 : ℝ))
      (E := (cell12389 ⟨13, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (1672535311139 / 2000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145850021373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_14 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (41796006145129 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (114585201649 / 5000000000000 : ℝ))
      (E := (cell12389 ⟨14, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (41796006145129 / 50000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (114585201649 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_15 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83557283637713 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291708026641 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨15, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83557283637713 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291708026641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_16 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83522579564927 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291712029791 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨16, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83522579564927 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291712029791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_17 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (20871975009423 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572929012061 / 25000000000000 : ℝ))
      (E := (cell12389 ⟨17, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (20871975009423 / 25000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (572929012061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_18 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83453245021977 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291720029373 / 100000000000000 : ℝ))
      (E := (cell12389 ⟨18, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83453245021977 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (2291720029373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12389_19 : CellCertificate 12389 (179117664253673 / 2000000000000000 : ℝ) (1695423526192639 / 1000000000000000000 : ℝ) (342678224230631 / 10000000000000000 : ℝ)
    (cell12389 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · norm_num [cell12389]
  · have h := gap_lower (n := 12389) (a := (83418614483927 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145862018329 / 50000000000000 : ℝ))
      (E := (cell12389 ⟨19, by decide⟩).energy) (xi := (342678224230631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12389 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12389]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12389])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12389) (a := (83418614483927 / 100000000000000 : ℝ)) (b := (166312590179 / 100000000000000 : ℝ)) (q := (1145862018329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12389])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12389]

theorem cert12390_0 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (84080797991873 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145755540591 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨0, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (84080797991873 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145755540591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_1 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (84045721861123 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145757531053 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨1, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (84045721861123 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145757531053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_2 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (42005335403943 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572879765181 / 25000000000000 : ℝ))
      (E := (cell12390 ⟨2, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (42005335403943 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572879765181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_3 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (5248477799709 / 6250000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572880771633 / 25000000000000 : ℝ))
      (E := (cell12390 ⟨3, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (5248477799709 / 6250000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572880771633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_4 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (10492580473359 / 12500000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145763545449 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨4, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (10492580473359 / 12500000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145763545449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_5 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83905667746039 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (286441385341 / 12500000000000 : ℝ))
      (E := (cell12390 ⟨5, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83905667746039 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (286441385341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_6 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83870716636607 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (229153507067 / 10000000000000 : ℝ))
      (E := (cell12390 ⟨6, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83870716636607 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (229153507067 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_7 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (163741778169 / 195312500000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572884765779 / 25000000000000 : ℝ))
      (E := (cell12390 ⟨7, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (163741778169 / 195312500000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572884765779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_8 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83800889067943 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291543068203 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨8, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83800889067943 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291543068203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_9 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83766012537181 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291547035823 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨9, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83766012537181 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291547035823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_10 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (2093279019869 / 2500000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458310206309 / 20000000000000 : ℝ))
      (E := (cell12390 ⟨10, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (2093279019869 / 2500000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458310206309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_11 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41848166902691 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291555004709 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨11, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41848166902691 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291555004709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_12 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (16732306306787 / 20000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291559020427 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨12, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (16732306306787 / 20000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291559020427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_13 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (5226672121593 / 6250000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572890756873 / 25000000000000 : ℝ))
      (E := (cell12390 ⟨13, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (5226672121593 / 6250000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (572890756873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_14 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (16718400201059 / 20000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145783516229 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨14, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (16718400201059 / 20000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145783516229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_15 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (8355727267879 / 10000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145785491751 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨15, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (8355727267879 / 10000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145785491751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_16 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41761284465793 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291575002921 / 100000000000000 : ℝ))
      (E := (cell12390 ⟨16, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41761284465793 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (2291575002921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_17 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (83487889729477 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458315796049 / 20000000000000 : ℝ))
      (E := (cell12390 ⟨17, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (83487889729477 / 100000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (458315796049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_18 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (2607913594951 / 3125000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (91663319167 / 4000000000000 : ℝ))
      (E := (cell12390 ⟨18, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (2607913594951 / 3125000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (91663319167 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12390_19 : CellCertificate 12390 (895559022838127 / 10000000000000000 : ℝ) (339057328403821 / 200000000000000000 : ℝ) (68529969820401 / 2000000000000000 : ℝ)
    (cell12390 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · norm_num [cell12390]
  · have h := gap_lower (n := 12390) (a := (41709302412299 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145793502519 / 50000000000000 : ℝ))
      (E := (cell12390 ⟨19, by decide⟩).energy) (xi := (68529969820401 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12390 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12390]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12390])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12390) (a := (41709302412299 / 50000000000000 : ℝ)) (b := (8314949647 / 5000000000000 : ℝ)) (q := (1145793502519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12390])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12390]

theorem cert12391_0 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (42040391048157 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291374114077 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨0, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (42040391048157 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291374114077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_1 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (84045706298073 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291378099611 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨1, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (84045706298073 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291378099611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_2 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (42005327788437 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (143211381477 / 6250000000000 : ℝ))
      (E := (cell12391 ⟨2, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (42005327788437 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (143211381477 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_3 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83975629895899 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572846519447 / 25000000000000 : ℝ))
      (E := (cell12391 ⟨3, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83975629895899 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (572846519447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_4 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (3357625168741 / 4000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291390089117 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨4, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (3357625168741 / 4000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291390089117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_5 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41952826754161 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291394088699 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨5, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41952826754161 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291394088699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_6 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83870702729051 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (35803095081 / 1562500000000 : ℝ))
      (E := (cell12391 ⟨6, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83870702729051 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (35803095081 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_7 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (20958944211167 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291402086961 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨7, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (20958944211167 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291402086961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_8 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (5237554738707 / 6250000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145703051083 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨8, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (5237554738707 / 6250000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145703051083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_9 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (20941499904329 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291410080689 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨9, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (20941499904329 / 25000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291410080689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_10 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83731148203197 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (22914140881 / 1000000000000 : ℝ))
      (E := (cell12391 ⟨10, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83731148203197 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (22914140881 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_11 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83696321541659 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291418073737 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨11, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83696321541659 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291418073737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_12 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83661519597589 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145711022327 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨12, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83661519597589 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145711022327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_13 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (4181337116803 / 5000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145713032867 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨13, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (4181337116803 / 5000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145713032867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_14 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (41795994861163 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (229143002739 / 10000000000000 : ℝ))
      (E := (cell12391 ⟨14, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (41795994861163 / 50000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (229143002739 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_15 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (4177863086091 / 5000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145717026059 / 50000000000000 : ℝ))
      (E := (cell12391 ⟨15, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (4177863086091 / 5000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (1145717026059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_16 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83522558300159 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (114571901487 / 5000000000000 : ℝ))
      (E := (cell12391 ⟨16, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83522558300159 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (114571901487 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_17 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (16697575884627 / 20000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (143215126511 / 6250000000000 : ℝ))
      (E := (cell12391 ⟨17, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (16697575884627 / 20000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (143215126511 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_18 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (83453225056719 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291446040997 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨18, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (83453225056719 / 100000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291446040997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12391_19 : CellCertificate 12391 (895529728959651 / 10000000000000000 : ℝ) (1695149779947143 / 1000000000000000000 : ℝ) (21413842423299 / 625000000000000 : ℝ)
    (cell12391 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · norm_num [cell12391]
  · have h := gap_lower (n := 12391) (a := (4170929758353 / 5000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291450027303 / 100000000000000 : ℝ))
      (E := (cell12391 ⟨19, by decide⟩).energy) (xi := (21413842423299 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12391 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12391]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12391])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12391) (a := (4170929758353 / 5000000000000 : ℝ)) (b := (41571349487 / 25000000000000 : ℝ)) (q := (2291450027303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12391])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12391]

theorem cert12392_0 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (21020191550831 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145618599807 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨0, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (21020191550831 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145618599807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_1 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (84045690737551 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (35800643591 / 1562500000000 : ℝ))
      (E := (cell12392 ⟨1, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (84045690737551 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (35800643591 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_2 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (21002660087087 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (458249039863 / 20000000000000 : ℝ))
      (E := (cell12392 ⟨2, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (21002660087087 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (458249039863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_3 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83975614998899 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572812294933 / 25000000000000 : ℝ))
      (E := (cell12392 ⟨3, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83975614998899 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (572812294933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_4 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83940614652581 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291253198113 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨4, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83940614652581 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291253198113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_5 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41952819636483 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145628602769 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨5, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41952819636483 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145628602769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_6 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (10483836102977 / 12500000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (458252242131 / 20000000000000 : ℝ))
      (E := (cell12392 ⟨6, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (10483836102977 / 12500000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (458252242131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_7 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83835763269087 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291265163909 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨7, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83835763269087 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291265163909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_8 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (2095021564323 / 2500000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291269189297 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨8, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (2095021564323 / 2500000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291269189297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_9 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83765986699649 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291273178789 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨9, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83765986699649 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291273178789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_10 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83731135613791 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291277139943 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨10, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83731135613791 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291277139943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_11 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83696309280051 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (143205071131 / 6250000000000 : ℝ))
      (E := (cell12392 ⟨11, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83696309280051 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (143205071131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_12 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83661507663319 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291285180369 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨12, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83661507663319 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291285180369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_13 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83626730728667 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291289157471 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨13, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83626730728667 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291289157471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_14 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (1671839568827 / 2000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229129313399 / 10000000000000 : ℝ))
      (E := (cell12392 ⟨14, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (1671839568827 / 2000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229129313399 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_15 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (20889312691701 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229129711623 / 10000000000000 : ℝ))
      (E := (cell12392 ⟨15, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (20889312691701 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (229129711623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_16 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (20880636917661 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291301110251 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨16, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (20880636917661 / 25000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291301110251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_17 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (16697573823733 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (286413140233 / 12500000000000 : ℝ))
      (E := (cell12392 ⟨17, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (16697573823733 / 20000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (286413140233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_18 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (83453215076839 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291309098439 / 100000000000000 : ℝ))
      (E := (cell12392 ⟨18, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (83453215076839 / 100000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (2291309098439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12392_19 : CellCertificate 12392 (35820017585273 / 400000000000000 : ℝ) (8475064699857 / 5000000000000000 : ℝ) (171296556620803 / 5000000000000000 : ℝ)
    (cell12392 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · norm_num [cell12392]
  · have h := gap_lower (n := 12392) (a := (41709292755657 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145656551727 / 50000000000000 : ℝ))
      (E := (cell12392 ⟨19, by decide⟩).energy) (xi := (171296556620803 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12392 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12392]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12392])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12392) (a := (41709292755657 / 50000000000000 : ℝ)) (b := (166271805203 / 100000000000000 : ℝ)) (q := (1145656551727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12392])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12392]

theorem cert12393_0 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (42040375156451 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572775098893 / 25000000000000 : ℝ))
      (E := (cell12393 ⟨0, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (42040375156451 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572775098893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_1 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (21011418794889 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291104390547 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨1, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (21011418794889 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291104390547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_2 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (21002656280577 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291108347771 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨2, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (21002656280577 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291108347771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_3 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83975600104343 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572778083629 / 25000000000000 : ℝ))
      (E := (cell12393 ⟨3, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83975600104343 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572778083629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_4 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (1049257501113 / 1250000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (143194772501 / 6250000000000 : ℝ))
      (E := (cell12393 ⟨4, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (1049257501113 / 1250000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (143194772501 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_5 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (20976406259993 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291120375349 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨5, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (20976406259993 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291120375349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_6 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41935337460451 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572781082811 / 25000000000000 : ℝ))
      (E := (cell12393 ⟨6, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41935337460451 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (572781082811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_7 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (16767149939157 / 20000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291128351903 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨7, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (16767149939157 / 20000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291128351903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_8 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83800849328767 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291132329597 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨8, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83800849328767 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291132329597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_9 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83765973784179 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (18329090641 / 800000000000 : ℝ))
      (E := (cell12393 ⟨9, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83765973784179 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (18329090641 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_10 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83731123026541 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145570151549 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨10, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83731123026541 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145570151549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_11 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (1046203712757 / 1250000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145572156927 / 50000000000000 : ℝ))
      (E := (cell12393 ⟨11, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (1046203712757 / 1250000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (1145572156927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_12 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (20915373932781 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291148311457 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨12, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (20915373932781 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291148311457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_13 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (20906679780827 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458230460541 / 20000000000000 : ℝ))
      (E := (cell12393 ⟨13, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (20906679780827 / 25000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458230460541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_14 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (5102048777 / 6103515625 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291156294151 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨14, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (5102048777 / 6103515625 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291156294151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_15 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (4177861990687 / 5000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291160292099 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨15, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (4177861990687 / 5000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291160292099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_16 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83522537043041 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291164302607 / 100000000000000 : ℝ))
      (E := (cell12393 ⟨16, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83522537043041 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (2291164302607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_17 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (41743929408033 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (229116827331 / 10000000000000 : ℝ))
      (E := (cell12393 ⟨17, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (41743929408033 / 50000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (229116827331 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_18 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83453205098789 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458234453581 / 20000000000000 : ℝ))
      (E := (cell12393 ⟨18, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83453205098789 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458234453581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12393_19 : CellCertificate 12393 (447735577426769 / 5000000000000000 : ℝ) (847438061043263 / 500000000000000000 : ℝ) (342564752507109 / 10000000000000000 : ℝ)
    (cell12393 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · norm_num [cell12393]
  · have h := gap_lower (n := 12393) (a := (83418575857359 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458235258343 / 20000000000000 : ℝ))
      (E := (cell12393 ⟨19, by decide⟩).energy) (xi := (342564752507109 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12393 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12393]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12393])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12393) (a := (83418575857359 / 100000000000000 : ℝ)) (b := (33251642941 / 20000000000000 : ℝ)) (q := (458235258343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12393])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12393]

theorem cert12394_0 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (10510091803131 / 12500000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572740896599 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨0, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (10510091803131 / 12500000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572740896599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_1 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (42022829812043 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (114548379309 / 5000000000000 : ℝ))
      (E := (cell12394 ⟨1, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (42022829812043 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (114548379309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_2 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (328166444917 / 390625000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (229097160683 / 10000000000000 : ℝ))
      (E := (cell12394 ⟨2, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (328166444917 / 390625000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (229097160683 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_3 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (8397558521223 / 10000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (286371949999 / 12500000000000 : ℝ))
      (E := (cell12394 ⟨3, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (8397558521223 / 10000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (286371949999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_4 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83940585527901 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572744893707 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨4, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83940585527901 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572744893707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_5 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41952805404669 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (28637294253 / 1250000000000 : ℝ))
      (E := (cell12394 ⟨5, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41952805404669 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (28637294253 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_6 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83870661020307 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2290987562793 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨6, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83870661020307 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2290987562793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_7 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41917868062381 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2290991535061 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨7, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41917868062381 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2290991535061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_8 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83800836086851 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2290995523069 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨8, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83800836086851 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2290995523069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_9 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (16753192174181 / 20000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145499767349 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨9, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (16753192174181 / 20000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145499767349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_10 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83731110441447 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572750879889 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨10, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83731110441447 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572750879889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_11 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83696284763183 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145503771491 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨11, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83696284763183 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145503771491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_12 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83661483801003 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572752888509 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨12, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83661483801003 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572752888509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_13 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83626707519983 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572753875359 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨13, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83626707519983 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572753875359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_14 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41795977942689 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572754876969 / 25000000000000 : ℝ))
      (E := (cell12394 ⟨14, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41795977942689 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (572754876969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_15 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (20889307215657 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291023521597 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨15, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (20889307215657 / 25000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291023521597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_16 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (1670450528347 / 2000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291027490503 / 100000000000000 : ℝ))
      (E := (cell12394 ⟨16, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (1670450528347 / 2000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (2291027490503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_17 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (83487848515339 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145515739257 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨17, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (83487848515339 / 100000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145515739257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_18 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (8345319512257 / 10000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145517745597 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨18, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (8345319512257 / 10000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145517745597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12394_19 : CellCertificate 12394 (2798255858199 / 31250000000000 : ℝ) (1694739326287173 / 1000000000000000000 : ℝ) (171268198283967 / 5000000000000000 : ℝ)
    (cell12394 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · norm_num [cell12394]
  · have h := gap_lower (n := 12394) (a := (41709283102597 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145519737821 / 50000000000000 : ℝ))
      (E := (cell12394 ⟨19, by decide⟩).energy) (xi := (171268198283967 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12394 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12394]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12394])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12394) (a := (41709283102597 / 50000000000000 : ℝ)) (b := (166244626453 / 100000000000000 : ℝ)) (q := (1145519737821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12394])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12394]

theorem cert12395_0 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (84080718539761 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572706721911 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨0, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (84080718539761 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572706721911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_1 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (42022822035571 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290830892327 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨1, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (42022822035571 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290830892327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_2 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (1050132433471 / 1250000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290834860843 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨2, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (1050132433471 / 1250000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290834860843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_3 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (131211828629 / 156250000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (143177428779 / 6250000000000 : ℝ))
      (E := (cell12395 ⟨3, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (131211828629 / 156250000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (143177428779 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_4 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20985142742291 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290842842549 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨4, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20985142742291 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290842842549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_5 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41952798290533 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (286355859237 / 12500000000000 : ℝ))
      (E := (cell12395 ⟨5, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41952798290533 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (286355859237 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_6 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83870647122031 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290850847383 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨6, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83870647122031 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290850847383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_7 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41917861278009 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145427414633 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨7, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41917861278009 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145427414633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_8 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20950205711793 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290858827679 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨8, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20950205711793 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290858827679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_9 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20941486989957 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290862850497 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨9, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20941486989957 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290862850497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_10 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20932774464627 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (229086684733 / 10000000000000 : ℝ))
      (E := (cell12395 ⟨10, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20932774464627 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (229086684733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_11 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (1046203406349 / 1250000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145435412739 / 50000000000000 : ℝ))
      (E := (cell12395 ⟨11, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (1046203406349 / 1250000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (1145435412739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_12 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (16732294374591 / 20000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (286359348999 / 12500000000000 : ℝ))
      (E := (cell12395 ⟨12, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (16732294374591 / 20000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (286359348999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_13 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (8362669591869 / 10000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290878811751 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨13, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (8362669591869 / 10000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290878811751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_14 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83591944610381 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458176555033 / 20000000000000 : ℝ))
      (E := (cell12395 ⟨14, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83591944610381 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458176555033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_15 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (20889304478367 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572721701181 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨15, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (20889304478367 / 25000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572721701181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_16 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83522515793569 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290890790249 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨16, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83522515793569 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290890790249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_17 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41743919108241 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458178959131 / 20000000000000 : ℝ))
      (E := (cell12395 ⟨17, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41743919108241 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (458178959131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_18 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (83453185148181 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572724692077 / 25000000000000 : ℝ))
      (E := (cell12395 ⟨18, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (83453185148181 / 100000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (572724692077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12395_19 : CellCertificate 12395 (895412598941141 / 10000000000000000 : ℝ) (1694602552567991 / 1000000000000000000 : ℝ) (342508045422721 / 10000000000000000 : ℝ)
    (cell12395 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · norm_num [cell12395]
  · have h := gap_lower (n := 12395) (a := (41709278277409 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290902771683 / 100000000000000 : ℝ))
      (E := (cell12395 ⟨19, by decide⟩).energy) (xi := (342508045422721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12395 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12395]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12395])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12395) (a := (41709278277409 / 50000000000000 : ℝ)) (b := (166231040447 / 100000000000000 : ℝ)) (q := (2290902771683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12395])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12395]

theorem cert12396_0 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (1051008783213 / 1250000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290690241541 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨0, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (1051008783213 / 1250000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290690241541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_1 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (84045628520723 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145347096693 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨1, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (84045628520723 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145347096693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_2 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (21002644864773 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (114534911273 / 5000000000000 : ℝ))
      (E := (cell12396 ⟨2, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (21002644864773 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (114534911273 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_3 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83975555435333 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290702173781 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨3, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83975555435333 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290702173781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_4 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (20985139103207 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145353110527 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨4, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (20985139103207 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145353110527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_5 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (5244098897197 / 6250000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572677550659 / 25000000000000 : ℝ))
      (E := (cell12396 ⟨5, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (5244098897197 / 6250000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572677550659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_6 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41935316613037 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (286339273127 / 12500000000000 : ℝ))
      (E := (cell12396 ⟨6, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41935316613037 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (286339273127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_7 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (1676714179791 / 2000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290718176583 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨7, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (1676714179791 / 2000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290718176583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_8 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83800809609729 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (286340273183 / 12500000000000 : ℝ))
      (E := (cell12396 ⟨8, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83800809609729 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (286340273183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_9 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (41882967525473 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572681540387 / 25000000000000 : ℝ))
      (E := (cell12396 ⟨9, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (41882967525473 / 50000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572681540387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_10 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (20932771319431 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290730170397 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨10, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (20932771319431 / 25000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290730170397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_11 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83696260254771 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145367080673 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨11, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83696260254771 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145367080673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_12 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83661459946981 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145369070721 / 50000000000000 : ℝ))
      (E := (cell12396 ⟨12, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83661459946981 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (1145369070721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_13 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (8362668431943 / 10000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290742175567 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨13, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (8362668431943 / 10000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290742175567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_14 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (2612247916793 / 3125000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290746154127 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨14, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (2612247916793 / 3125000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290746154127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_15 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83557206966259 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572687535371 / 25000000000000 : ℝ))
      (E := (cell12396 ⟨15, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83557206966259 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (572687535371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_16 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (835225051717 / 1000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290754143691 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨16, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (835225051717 / 1000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290754143691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_17 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (10435978489937 / 12500000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290758108381 / 100000000000000 : ℝ))
      (E := (cell12396 ⟨17, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (10435978489937 / 12500000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (2290758108381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_18 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83453175175623 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (143172631203 / 6250000000000 : ℝ))
      (E := (cell12396 ⟨18, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83453175175623 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (143172631203 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12396_19 : CellCertificate 12396 (223845831951203 / 2500000000000000 : ℝ) (1694465800923637 / 1000000000000000000 : ℝ) (342479699070111 / 10000000000000000 : ℝ)
    (cell12396 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · norm_num [cell12396]
  · have h := gap_lower (n := 12396) (a := (83418546906233 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458153224323 / 20000000000000 : ℝ))
      (E := (cell12396 ⟨19, by decide⟩).energy) (xi := (342479699070111 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12396 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12396]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12396])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12396) (a := (83418546906233 / 100000000000000 : ℝ)) (b := (33243491337 / 20000000000000 : ℝ)) (q := (458153224323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12396])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12396]

theorem cert12397_0 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (21020171694221 / 25000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290553590311 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨0, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (21020171694221 / 25000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290553590311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_1 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (84045612972829 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290557604963 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨1, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (84045612972829 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290557604963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_2 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (84010564242987 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458112317007 / 20000000000000 : ℝ))
      (E := (cell12397 ⟨2, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (84010564242987 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458112317007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_3 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83975540550547 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458113119559 / 20000000000000 : ℝ))
      (E := (cell12397 ⟨3, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83975540550547 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458113119559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_4 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (20985135464723 / 25000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290569594601 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨4, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (20985135464723 / 25000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290569594601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_5 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (41952784065799 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145286792177 / 50000000000000 : ℝ))
      (E := (cell12397 ⟨5, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (41952784065799 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145286792177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_6 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (16774123866487 / 20000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458115515139 / 20000000000000 : ℝ))
      (E := (cell12397 ⟨6, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (16774123866487 / 20000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (458115515139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_7 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (1047946192817 / 1250000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290581577009 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨7, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (1047946192817 / 1250000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290581577009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_8 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83800796374523 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (91623423857 / 4000000000000 : ℝ))
      (E := (cell12397 ⟨8, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83800796374523 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (91623423857 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_9 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83765922144259 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (229058958383 / 10000000000000 : ℝ))
      (E := (cell12397 ⟨9, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83765922144259 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (229058958383 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_10 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (41865536349547 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290593546771 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨10, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (41865536349547 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290593546771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_11 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (10462031000467 / 12500000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145298775293 / 50000000000000 : ℝ))
      (E := (cell12397 ⟨11, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (10462031000467 / 12500000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145298775293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_12 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83661448023079 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290601544331 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨12, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83661448023079 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290601544331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_13 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83626672722201 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572651383701 / 25000000000000 : ℝ))
      (E := (cell12397 ⟨13, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83626672722201 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (572651383701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_14 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (41795961033181 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (286326191069 / 12500000000000 : ℝ))
      (E := (cell12397 ⟨14, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (41795961033181 / 50000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (286326191069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_15 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83557196021001 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290613531877 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨15, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83557196021001 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290613531877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_16 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83522494551741 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290617550831 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨16, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83522494551741 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290617550831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_17 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83487817624379 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290621533047 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨17, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83487817624379 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290621533047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_18 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (83453165204893 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145312771109 / 50000000000000 : ℝ))
      (E := (cell12397 ⟨18, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (83453165204893 / 100000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (1145312771109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12397_19 : CellCertificate 12397 (895354061213583 / 10000000000000000 : ℝ) (847164535674383 / 500000000000000000 : ℝ) (171225678754373 / 5000000000000000 : ℝ)
    (cell12397 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · norm_num [cell12397]
  · have h := gap_lower (n := 12397) (a := (20854634314859 / 25000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290629525441 / 100000000000000 : ℝ))
      (E := (cell12397 ⟨19, by decide⟩).energy) (xi := (171225678754373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12397 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12397]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12397])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12397) (a := (20854634314859 / 25000000000000 : ℝ)) (b := (166203875167 / 100000000000000 : ℝ)) (q := (2290629525441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12397])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12397]

theorem cert12398_0 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (42040335449647 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290417107287 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨0, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (42040335449647 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290417107287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_1 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (42022798713729 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290421069257 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨1, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (42022798713729 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290421069257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_2 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (21002637257341 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290425055217 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨2, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (21002637257341 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290425055217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_3 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83975525668201 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145214537329 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨3, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83975525668201 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145214537329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_4 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (16788105461471 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (458086615787 / 20000000000000 : ℝ))
      (E := (cell12398 ⟨4, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (16788105461471 / 20000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (458086615787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_5 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83905553910403 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572609269237 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨5, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83905553910403 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572609269237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_6 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83870605441113 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290441019419 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨6, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83870605441113 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290441019419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_7 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41917840931723 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290445030547 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨7, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41917840931723 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290445030547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_8 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (5237548946347 / 6250000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290449060563 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨8, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (5237548946347 / 6250000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290449060563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_9 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83765909239767 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145226529677 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨9, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83765909239767 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145226529677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_10 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41865530061309 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145228517233 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨10, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41865530061309 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145228517233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_11 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83696235754813 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572615262809 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨11, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83696235754813 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572615262809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_12 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83661436101249 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145232500329 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨12, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83661436101249 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145232500329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_13 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (20906665281751 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290469005627 / 100000000000000 : ℝ))
      (E := (cell12398 ⟨13, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (20906665281751 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (2290469005627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_14 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (41795955398669 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572618253663 / 25000000000000 : ℝ))
      (E := (cell12398 ⟨14, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (41795955398669 / 50000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (572618253663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_15 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83557185077693 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (71577405497 / 3125000000000 : ℝ))
      (E := (cell12398 ⟨15, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83557185077693 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (71577405497 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_16 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83522483933691 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (286310126459 / 12500000000000 : ℝ))
      (E := (cell12398 ⟨16, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83522483933691 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (286310126459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_17 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (20871951832783 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145242505739 / 50000000000000 : ℝ))
      (E := (cell12398 ⟨17, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (20871951832783 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (1145242505739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_18 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (83453155235993 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (143155561301 / 6250000000000 : ℝ))
      (E := (cell12398 ⟨18, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (83453155235993 / 100000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (143155561301 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12398_19 : CellCertificate 12398 (179064959833269 / 2000000000000000 : ℝ) (423548090959509 / 250000000000000000 : ℝ) (85605755184317 / 2500000000000000 : ℝ)
    (cell12398 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · norm_num [cell12398]
  · have h := gap_lower (n := 12398) (a := (20854631903607 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (57262324579 / 2500000000000 : ℝ))
      (E := (cell12398 ⟨19, by decide⟩).energy) (xi := (85605755184317 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12398 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12398]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12398])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12398) (a := (20854631903607 / 25000000000000 : ℝ)) (b := (166190295893 / 100000000000000 : ℝ)) (q := (57262324579 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12398])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12398]

theorem cert12399_0 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (84080655024269 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145140309569 / 50000000000000 : ℝ))
      (E := (cell12399 ⟨0, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (84080655024269 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145140309569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_1 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (8404558188461 / 10000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (229028458627 / 10000000000000 : ℝ))
      (E := (cell12399 ⟨1, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (8404558188461 / 10000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (229028458627 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_2 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (42005266909111 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (458057715637 / 20000000000000 : ℝ))
      (E := (cell12399 ⟨2, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (42005266909111 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (458057715637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_3 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83975510788297 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290292604371 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨3, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83975510788297 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290292604371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_4 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41970256379109 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290296558313 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨4, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41970256379109 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290296558313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_5 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (16781107938313 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290300564629 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨5, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (16781107938313 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290300564629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_6 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (20967647888027 / 25000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290304574111 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨6, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (20967647888027 / 25000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290304574111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_7 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (1309932317247 / 1562500000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290308595141 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨7, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (1309932317247 / 1562500000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290308595141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_8 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (16760153982163 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290312577881 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨8, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (16760153982163 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290312577881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_9 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83765896337469 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290316530133 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨9, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83765896337469 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290316530133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_10 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41865523774147 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290320575471 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨10, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41865523774147 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290320575471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_11 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83696223508003 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286290568403 / 12500000000000 : ℝ))
      (E := (cell12399 ⟨11, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83696223508003 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286290568403 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_12 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83661424181491 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145164284243 / 50000000000000 : ℝ))
      (E := (cell12399 ⟨12, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83661424181491 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (1145164284243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_13 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (41813324766919 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572583132489 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨13, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (41813324766919 / 50000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572583132489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_14 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (16718379906061 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572584138581 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨14, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (16718379906061 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572584138581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_15 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (16711434827267 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290340531697 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨15, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (16711434827267 / 20000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290340531697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_16 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83522473317551 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572586131553 / 25000000000000 : ℝ))
      (E := (cell12399 ⟨16, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83522473317551 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (572586131553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_17 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (83487797039753 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (91613941747 / 4000000000000 : ℝ))
      (E := (cell12399 ⟨17, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (83487797039753 / 100000000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (91613941747 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_18 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (2086328631723 / 2500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290352531447 / 100000000000000 : ℝ))
      (E := (cell12399 ⟨18, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (2086328631723 / 2500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (2290352531447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

theorem cert12399_19 : CellCertificate 12399 (89529554166199 / 1000000000000000 : ℝ) (423513919596527 / 250000000000000000 : ℝ) (342394688754321 / 10000000000000000 : ℝ)
    (cell12399 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · norm_num [cell12399]
  · have h := gap_lower (n := 12399) (a := (10427314746401 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286294561847 / 12500000000000 : ℝ))
      (E := (cell12399 ⟨19, by decide⟩).energy) (xi := (342394688754321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12399 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12399]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12399])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12399) (a := (10427314746401 / 12500000000000 : ℝ)) (b := (83088359431 / 50000000000000 : ℝ)) (q := (286294561847 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12399])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12399]

end BstLean.Part268
