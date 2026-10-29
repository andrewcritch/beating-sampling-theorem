import BstLean.Part268CellShard33Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13175_20 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83375970233339 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196427203403 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨20, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83375970233339 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196427203403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_21 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83341571452363 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274553903913 / 12500000000000 : ℝ))
      (E := (cell13175 ⟨21, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83341571452363 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274553903913 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_22 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83307196794103 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549108816703 / 25000000000000 : ℝ))
      (E := (cell13175 ⟨22, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83307196794103 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549108816703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_23 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83272846225913 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549109813711 / 25000000000000 : ℝ))
      (E := (cell13175 ⟨23, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83272846225913 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549109813711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_24 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83238519715313 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274555407103 / 12500000000000 : ℝ))
      (E := (cell13175 ⟨24, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83238519715313 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274555407103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_25 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (20801054307497 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196447275597 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨25, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (20801054307497 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196447275597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_26 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (649765146389 / 781250000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (219645131377 / 10000000000000 : ℝ))
      (E := (cell13175 ⟨26, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (649765146389 / 781250000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (219645131377 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_27 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83135684206739 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549113828809 / 25000000000000 : ℝ))
      (E := (cell13175 ⟨27, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83135684206739 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549113828809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_28 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (8310145360501 / 10000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196459340581 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨28, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (8310145360501 / 10000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196459340581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_29 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (83067246900947 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549115833297 / 25000000000000 : ℝ))
      (E := (cell13175 ⟨29, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (83067246900947 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549115833297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_30 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (20758266015763 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (137279209577 / 6250000000000 : ℝ))
      (E := (cell13175 ⟨30, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (20758266015763 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (137279209577 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_31 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82998905059991 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196471402173 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨31, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82998905059991 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196471402173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_32 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (16592953972117 / 20000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098237711319 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨32, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (16592953972117 / 20000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098237711319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_33 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (10366332304227 / 12500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196479415563 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨33, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (10366332304227 / 12500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196479415563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_34 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82896570748823 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (219648344031 / 10000000000000 : ℝ))
      (E := (cell13175 ⟨34, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82896570748823 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (219648344031 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_35 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82862506774901 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (54912185969 / 2500000000000 : ℝ))
      (E := (cell13175 ⟨35, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82862506774901 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (54912185969 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_36 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (41414233240751 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196491469873 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨36, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (41414233240751 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196491469873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_37 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (10349306229779 / 12500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (439299095007 / 20000000000000 : ℝ))
      (E := (cell13175 ⟨37, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (10349306229779 / 12500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (439299095007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_38 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (323283034433 / 390625000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196499512811 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨38, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (323283034433 / 390625000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196499512811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_39 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (5170405461329 / 6250000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098251762049 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨39, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (5170405461329 / 6250000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098251762049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13176_20 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83375956301449 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196316711909 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨20, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83375956301449 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196316711909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_21 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83341557526603 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196320737273 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨21, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83341557526603 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196320737273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_22 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83307182874469 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196324770289 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨22, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83307182874469 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196324770289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_23 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83272832312399 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196328755877 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨23, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83272832312399 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196328755877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_24 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41619252903957 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196332813877 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨24, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41619252903957 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196332813877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_25 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83204203328699 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196336830321 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨25, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83204203328699 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196336830321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_26 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41584962421303 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (8785363231 / 400000000000 : ℝ))
      (E := (cell13176 ⟨26, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41584962421303 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (8785363231 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_27 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83135670317653 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549086216361 / 25000000000000 : ℝ))
      (E := (cell13176 ⟨27, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83135670317653 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549086216361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_28 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41550719861009 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196348888601 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨28, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41550719861009 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196348888601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_29 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83067233024043 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098176439533 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨29, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83067233024043 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098176439533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_30 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (83033050192233 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098178448507 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨30, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (83033050192233 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098178448507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_31 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (331995564781 / 400000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549090221331 / 25000000000000 : ℝ))
      (E := (cell13176 ⟨31, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (331995564781 / 400000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549090221331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_32 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82964756001917 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196364903763 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨32, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82964756001917 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196364903763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_33 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82930644581217 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (274546119167 / 12500000000000 : ℝ))
      (E := (cell13176 ⟨33, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82930644581217 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (274546119167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_34 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82896556902287 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196372976173 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨34, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82896556902287 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196372976173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_35 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (10357811616803 / 12500000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196376972759 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨35, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (10357811616803 / 12500000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196376972759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_36 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41414226323539 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098190501027 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨36, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41414226323539 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098190501027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_37 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (646831531327 / 781250000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549096251361 / 25000000000000 : ℝ))
      (E := (cell13176 ⟨37, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (646831531327 / 781250000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549096251361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_38 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (20690110748129 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (439277808299 / 20000000000000 : ℝ))
      (E := (cell13176 ⟨38, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (20690110748129 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (439277808299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_39 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (8272647356497 / 10000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196393051103 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨39, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (8272647356497 / 10000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196393051103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13177_20 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (20843985592919 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196206274557 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨20, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (20843985592919 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196206274557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_21 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (1041769295037 / 1250000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196210297407 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨21, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (1041769295037 / 1250000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196210297407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_22 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (1666143379139 / 2000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196214327957 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨22, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (1666143379139 / 2000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196214327957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_23 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83272818401 / 100000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549054577781 / 25000000000000 : ℝ))
      (E := (cell13177 ⟨23, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83272818401 / 100000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549054577781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_24 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (20809622975657 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196222366751 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨24, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (20809622975657 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196222366751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_25 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83204189429521 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196226380869 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨25, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83204189429521 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196226380869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_26 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83169910949533 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439246071203 / 20000000000000 : ℝ))
      (E := (cell13177 ⟨26, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83169910949533 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439246071203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_27 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83135656430677 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196234411477 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨27, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83135656430677 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196234411477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_28 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (5193839115071 / 6250000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439247686489 / 20000000000000 : ℝ))
      (E := (cell13177 ⟨28, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (5193839115071 / 6250000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439247686489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_29 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83067219149249 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196242420769 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨29, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83067219149249 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196242420769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_30 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (83033036323521 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196246436623 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨30, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (83033036323521 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196246436623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_31 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (10374859666577 / 12500000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439250096293 / 20000000000000 : ℝ))
      (E := (cell13177 ⟨31, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (10374859666577 / 12500000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439250096293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_32 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (20741185536339 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098127248963 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨32, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (20741185536339 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098127248963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_33 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82930630730723 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098129243469 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨33, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82930630730723 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098129243469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_34 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (1295258485279 / 1562500000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098131253933 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨34, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (1295258485279 / 1562500000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098131253933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_35 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (1657249581921 / 2000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549066625647 / 25000000000000 : ℝ))
      (E := (cell13177 ⟨35, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (1657249581921 / 2000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549066625647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_36 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82828438814757 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098135265033 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨36, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82828438814757 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098135265033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_37 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (41397211091791 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098137265843 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨37, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (41397211091791 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098137265843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_38 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (20690107293071 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196278566013 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨38, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (20690107293071 / 25000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196278566013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_39 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (3309058390031 / 4000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196282573943 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨39, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (3309058390031 / 4000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196282573943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13178_20 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (4168796422201 / 5000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (34313997391 / 1562500000000 : ℝ))
      (E := (cell13178 ⟨20, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (4168796422201 / 5000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (34313997391 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_21 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83341529681433 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196099853361 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨21, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83341529681433 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196099853361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_22 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83307155041547 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439220776289 / 20000000000000 : ℝ))
      (E := (cell13178 ⟨22, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83307155041547 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439220776289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_23 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (41636402245857 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098053931097 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨23, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (41636402245857 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098053931097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_24 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (16647695599891 / 20000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (274513989431 / 12500000000000 : ℝ))
      (E := (cell13178 ⟨24, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (16647695599891 / 20000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (274513989431 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_25 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (10400521941557 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196115927239 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨25, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (10400521941557 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196115927239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_26 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (8316989705857 / 10000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196119958571 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨26, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (8316989705857 / 10000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196119958571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_27 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20783910636453 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098061976667 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨27, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20783910636453 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098061976667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_28 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83101411962363 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439225594423 / 20000000000000 : ℝ))
      (E := (cell13178 ⟨28, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83101411962363 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439225594423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_29 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83067205276563 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196131958299 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨29, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83067205276563 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196131958299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_30 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (83033022456917 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196135972059 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨30, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (83033022456917 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196135972059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_31 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (10374857934011 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439228002971 / 20000000000000 : ℝ))
      (E := (cell13178 ⟨31, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (10374857934011 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439228002971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_32 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (829647282909 / 1000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196144029313 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨32, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (829647282909 / 1000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196144029313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_33 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (41465308441167 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196148074999 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨33, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (41465308441167 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196148074999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_34 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (10362066151941 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098076047021 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨34, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (10362066151941 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098076047021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_35 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (82862465259779 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (87846243477 / 4000000000000 : ℝ))
      (E := (cell13178 ⟨35, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (82862465259779 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (87846243477 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_36 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (82828424984537 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (219616011261 / 10000000000000 : ℝ))
      (E := (cell13178 ⟨36, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (82828424984537 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (219616011261 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_37 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (5174650522463 / 6250000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439232822497 / 20000000000000 : ℝ))
      (E := (cell13178 ⟨37, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (5174650522463 / 6250000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439232822497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_38 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (10345051919269 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196168145111 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨38, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (10345051919269 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196168145111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_39 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (2068161148467 / 2500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098086075693 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨39, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (2068161148467 / 2500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098086075693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13179_20 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83375914518481 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195985387309 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨20, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83375914518481 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2195985387309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_21 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83341515762021 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (137249337821 / 6250000000000 : ℝ))
      (E := (cell13179 ⟨21, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83341515762021 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (137249337821 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_22 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83307141128257 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (548998357689 / 25000000000000 : ℝ))
      (E := (cell13179 ⟨22, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83307141128257 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (548998357689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_23 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41636395292271 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (54899936687 / 2500000000000 : ℝ))
      (E := (cell13179 ⟨23, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41636395292271 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (54899936687 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_24 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (16647692819679 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (8578130703 / 390625000000 : ℝ))
      (E := (cell13179 ⟨24, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (16647692819679 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (8578130703 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_25 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83204161637503 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1098002734717 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨25, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83204161637503 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1098002734717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_26 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41584941584859 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196009498487 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨26, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41584941584859 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196009498487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_27 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (83135628663057 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (439202709901 / 20000000000000 : ℝ))
      (E := (cell13179 ⟨27, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (83135628663057 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (439202709901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_28 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41550699042849 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (17568140529 / 800000000000 : ℝ))
      (E := (cell13179 ⟨28, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41550699042849 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (17568140529 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_29 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (16613438281197 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (137251346887 / 6250000000000 : ℝ))
      (E := (cell13179 ⟨29, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (16613438281197 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (137251346887 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_30 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (4151650429621 / 5000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196025561881 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨30, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (4151650429621 / 5000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196025561881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_31 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82998849613667 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1098014801327 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨31, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82998849613667 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1098014801327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_32 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82964714438549 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (68626050473 / 3125000000000 : ℝ))
      (E := (cell13179 ⟨32, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82964714438549 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (68626050473 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_33 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82930603036049 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196037658891 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨33, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82930603036049 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196037658891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_34 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (10362064421913 / 12500000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196041676049 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨34, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (10362064421913 / 12500000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196041676049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_35 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (8286245142561 / 10000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1098022833547 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨35, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (8286245142561 / 10000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1098022833547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_36 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82828411156419 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (549012422747 / 25000000000000 : ℝ))
      (E := (cell13179 ⟨36, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82828411156419 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (549012422747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_37 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (10349299317167 / 12500000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (549013422279 / 25000000000000 : ℝ))
      (E := (cell13179 ⟨37, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (10349299317167 / 12500000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (549013422279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_38 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (2069010038453 / 2500000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196057720043 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨38, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (2069010038453 / 2500000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196057720043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_39 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82726432128683 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196061724667 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨39, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82726432128683 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196061724667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13180_20 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83375900595057 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195874995741 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨20, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83375900595057 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195874995741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_21 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (20835375461181 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195879011081 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨21, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (20835375461181 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195879011081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_22 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41653563608541 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195883034259 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨22, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41653563608541 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195883034259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_23 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83272776679483 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195887068589 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨23, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83272776679483 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195887068589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_24 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83238450199447 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (219589105873 / 10000000000000 : ℝ))
      (E := (cell13180 ⟨24, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83238450199447 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (219589105873 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_25 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83204147744661 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (137243445271 / 6250000000000 : ℝ))
      (E := (cell13180 ⟨25, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83204147744661 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (137243445271 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_26 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83169869282977 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195899092693 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨26, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83169869282977 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195899092693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_27 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83135614782411 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195903141503 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨27, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83135614782411 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195903141503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_28 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41550692105571 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097953577981 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨28, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41550692105571 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097953577981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_29 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41533588768757 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097955568957 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨29, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41533588768757 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097955568957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_30 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (83032994730029 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195915206093 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨30, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (83032994730029 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195915206093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_31 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82998835757351 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (439183837257 / 20000000000000 : ℝ))
      (E := (cell13180 ⟨31, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82998835757351 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (439183837257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_32 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (5185293786769 / 6250000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (219592319679 / 10000000000000 : ℝ))
      (E := (cell13180 ⟨32, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (5185293786769 / 6250000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (219592319679 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_33 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (20732647297967 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (274490904827 / 12500000000000 : ℝ))
      (E := (cell13180 ⟨33, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (20732647297967 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (274490904827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_34 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41448250768591 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (219593125389 / 10000000000000 : ℝ))
      (E := (cell13180 ⟨34, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41448250768591 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (219593125389 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_35 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82862437593543 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097967621549 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨35, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82862437593543 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097967621549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_36 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41414198665201 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (5489848163 / 250000000000 : ℝ))
      (E := (cell13180 ⟨36, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41414198665201 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (5489848163 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_37 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82794380717363 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195943320307 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨37, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82794380717363 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195943320307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_38 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82760387724187 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195947349559 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨38, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82760387724187 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195947349559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_39 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (16545283664157 / 20000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195951352553 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨39, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (16545283664157 / 20000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195951352553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13181_20 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (20843971668437 / 25000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195764658321 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨20, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (20843971668437 / 25000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195764658321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_21 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83341487929541 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195768671197 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨21, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83341487929541 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195768671197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_22 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (4165355665401 / 5000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195772691959 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨22, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (4165355665401 / 5000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195772691959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_23 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (10409095347067 / 12500000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (87831066621 / 4000000000000 : ℝ))
      (E := (cell13181 ⟨23, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (10409095347067 / 12500000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (87831066621 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_24 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (8323843630261 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195780711737 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨24, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (8323843630261 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195780711737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_25 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83204133853929 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (17566277733 / 800000000000 : ℝ))
      (E := (cell13181 ⟨25, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83204133853929 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (17566277733 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_26 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (16633971079669 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195788741193 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨26, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (16633971079669 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195788741193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_27 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (83135600903873 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548948182333 / 25000000000000 : ℝ))
      (E := (cell13181 ⟨27, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (83135600903873 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (548948182333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_28 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41550685169347 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195796741629 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨28, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41550685169347 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195796741629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_29 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (1661343273423 / 2000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195800780001 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨29, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (1661343273423 / 2000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195800780001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_30 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (16606596173949 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195804787577 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨30, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (16606596173949 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195804787577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_31 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82998821903141 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (274476103041 / 12500000000000 : ℝ))
      (E := (cell13181 ⟨31, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82998821903141 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (274476103041 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_32 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41482343370081 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195812832883 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨32, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41482343370081 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195812832883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_33 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (8293057534979 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195816872803 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨33, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (8293057534979 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195816872803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_34 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82896487701163 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097910443109 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨34, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82896487701163 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097910443109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_35 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41431211881789 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195824873613 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨35, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41431211881789 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195824873613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_36 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (16565676701297 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195828893949 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨36, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (16565676701297 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195828893949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_37 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (8279436689949 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (439166589467 / 20000000000000 : ℝ))
      (E := (cell13181 ⟨37, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (8279436689949 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (439166589467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_38 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (2586261684761 / 3125000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (274479614521 / 12500000000000 : ℝ))
      (E := (cell13181 ⟨38, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (2586261684761 / 3125000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (274479614521 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_39 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (10340800564373 / 12500000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (54896024407 / 2500000000000 : ℝ))
      (E := (cell13181 ⟨39, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (10340800564373 / 12500000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (54896024407 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13182_20 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (16675174550911 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097827129199 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨20, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (16675174550911 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097827129199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_21 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83341474016473 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548914567197 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨21, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83341474016473 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548914567197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_22 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83307099401071 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274457785889 / 12500000000000 : ℝ))
      (E := (cell13182 ⟨22, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83307099401071 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274457785889 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_23 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83272748875701 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (54891657917 / 2500000000000 : ℝ))
      (E := (cell13182 ⟨23, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83272748875701 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (54891657917 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_24 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (16647684481577 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195670360569 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨24, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (16647684481577 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195670360569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_25 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20801029991327 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195674363181 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨25, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20801029991327 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195674363181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_26 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (41584920757911 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (27445979819 / 1250000000000 : ℝ))
      (E := (cell13182 ⟨26, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (41584920757911 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (27445979819 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_27 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20783896756861 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548920592869 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨27, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20783896756861 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548920592869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_28 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (41550678234177 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548921595409 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨28, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (41550678234177 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548921595409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_29 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (83067149806893 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097845208959 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨29, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (83067149806893 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097845208959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_30 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (16606593402313 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195694423451 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨30, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (16606593402313 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195694423451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_31 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (16599761610207 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (439139691641 / 20000000000000 : ℝ))
      (E := (cell13182 ⟨31, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (16599761610207 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (439139691641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_32 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20741168223531 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274462808101 / 12500000000000 : ℝ))
      (E := (cell13182 ⟨32, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20741168223531 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274462808101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_33 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (41465280754907 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (87828260113 / 4000000000000 : ℝ))
      (E := (cell13182 ⟨33, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (41465280754907 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (87828260113 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_34 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (41448236933623 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195710514381 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨34, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (41448236933623 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195710514381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_35 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82862409935713 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548928624991 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨35, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82862409935713 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548928624991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_36 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20707092421167 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097859259267 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨36, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20707092421167 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097859259267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_37 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20698588270929 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195722570201 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨37, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20698588270929 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195722570201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_38 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (10345045012827 / 12500000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097863298053 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨38, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (10345045012827 / 12500000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097863298053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_39 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (1034079883891 / 1250000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (439146119169 / 20000000000000 : ℝ))
      (E := (cell13182 ⟨39, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (1034079883891 / 1250000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (439146119169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13183_20 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (3335034353499 / 4000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (137221494539 / 6250000000000 : ℝ))
      (E := (cell13183 ⟨20, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (3335034353499 / 4000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (137221494539 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_21 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83341460105517 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195547978901 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨21, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83341460105517 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195547978901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_22 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41653542748117 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195551994833 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨22, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41653542748117 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195551994833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_23 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41636367488489 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097777981831 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨23, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41636367488489 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097777981831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_24 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (8323840851527 / 10000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195560005229 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨24, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (8323840851527 / 10000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195560005229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_25 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (20801026519699 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097782002783 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨25, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (20801026519699 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097782002783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_26 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (5198114227213 / 6250000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195568025677 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨26, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (5198114227213 / 6250000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195568025677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_27 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83135573153123 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097786033969 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨27, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83135573153123 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097786033969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_28 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (2077533565003 / 2500000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195576075987 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨28, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (2077533565003 / 2500000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195576075987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_29 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41533567972371 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097790055101 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨29, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41533567972371 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097790055101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_30 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (83032953155491 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548896028429 / 25000000000000 : ℝ))
      (E := (cell13183 ⟨30, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (83032953155491 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548896028429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_31 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (82998794201033 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195588146497 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨31, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (82998794201033 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195588146497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_32 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (82964659050189 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097796075587 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨32, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (82964659050189 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097796075587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_33 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41465273835971 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (54889903217 / 2500000000000 : ℝ))
      (E := (cell13183 ⟨33, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41465273835971 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (54889903217 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_34 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (8289646003543 / 10000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195600197031 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨34, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (8289646003543 / 10000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195600197031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_35 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (82862396109949 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195604180827 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨35, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (82862396109949 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195604180827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_36 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (82828355864951 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439121639531 / 20000000000000 : ℝ))
      (E := (cell13183 ⟨36, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (82828355864951 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439121639531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_37 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (2069858481751 / 2500000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548903061907 / 25000000000000 : ℝ))
      (E := (cell13183 ⟨37, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (2069858481751 / 2500000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548903061907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_38 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (82760346294977 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548904067971 / 25000000000000 : ℝ))
      (E := (cell13183 ⟨38, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (82760346294977 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548904067971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_39 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41363188454837 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195620270019 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨39, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41363188454837 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195620270019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13184_20 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (8337584492251 / 10000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195433620999 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨20, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (8337584492251 / 10000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195433620999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_21 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (3333657847867 / 4000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (548859406623 / 25000000000000 : ℝ))
      (E := (cell13184 ⟨21, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (3333657847867 / 4000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (548859406623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_22 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83307071593509 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195441640011 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨22, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83307071593509 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195441640011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_23 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (41636360540183 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097722832433 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨23, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (41636360540183 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097722832433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_24 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (16647678924953 / 20000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195449704137 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨24, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (16647678924953 / 20000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195449704137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_25 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83204092194393 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195453702223 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨25, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83204092194393 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195453702223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_26 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (41584906878551 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195457720129 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨26, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (41584906878551 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195457720129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_27 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83135559280909 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (137216356359 / 6250000000000 : ℝ))
      (E := (cell13184 ⟨27, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83135559280909 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (137216356359 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_28 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (83101328733993 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195465766169 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨28, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (83101328733993 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195465766169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_29 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (10383390260587 / 12500000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439093947957 / 20000000000000 : ℝ))
      (E := (cell13184 ⟨29, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (10383390260587 / 12500000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439093947957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_30 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (41516469650761 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439094759963 / 20000000000000 : ℝ))
      (E := (cell13184 ⟨30, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (41516469650761 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439094759963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_31 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (41499390176567 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195477772043 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨31, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (41499390176567 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195477772043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_32 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82964645208357 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (17563854667 / 800000000000 : ℝ))
      (E := (cell13184 ⟨32, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82964645208357 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (17563854667 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_33 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82930533836171 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097742904501 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨33, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82930533836171 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097742904501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_34 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (16579289241143 / 20000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (6860905861 / 312500000000 : ℝ))
      (E := (cell13184 ⟨34, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (16579289241143 / 20000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (6860905861 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_35 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (16572476457257 / 20000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195493857529 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨35, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (16572476457257 / 20000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195493857529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_36 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82828342047333 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (274437234077 / 12500000000000 : ℝ))
      (E := (cell13184 ⟨36, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82828342047333 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (274437234077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_37 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82794325458463 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097750960447 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨37, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82794325458463 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097750960447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_38 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (20690083122359 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097752971751 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨38, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (20690083122359 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097752971751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_39 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82726363110163 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195509940037 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨39, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82726363110163 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195509940037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13185_20 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41687915504829 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195323325201 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨20, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41687915504829 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195323325201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_21 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (16668286457989 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195327328257 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨21, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (16668286457989 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195327328257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_22 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (2603345552903 / 3125000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195331339387 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨22, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (2603345552903 / 3125000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195331339387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_23 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (16654541437173 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195335361899 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨23, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (16654541437173 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195335361899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_24 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (8323838073637 / 10000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097669699437 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨24, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (8323838073637 / 10000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097669699437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_25 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (83204078312099 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (219534339471 / 10000000000000 : ℝ))
      (E := (cell13185 ⟨25, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (83204078312099 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (219534339471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_26 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (16633959976181 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548836852603 / 25000000000000 : ℝ))
      (E := (cell13185 ⟨26, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (16633959976181 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548836852603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_27 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41567772705401 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195351448359 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨27, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41567772705401 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195351448359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_28 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (20775328717493 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439071090437 / 20000000000000 : ℝ))
      (E := (cell13185 ⟨28, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (20775328717493 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439071090437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_29 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (16613421645351 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195359482273 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨29, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (16613421645351 / 20000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195359482273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_30 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (83032925449657 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195363481749 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨30, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (83032925449657 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195363481749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_31 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82998766507339 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548841877647 / 25000000000000 : ℝ))
      (E := (cell13185 ⟨31, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82998766507339 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548841877647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_32 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82964631368627 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195371511413 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨32, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82964631368627 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195371511413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_33 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82930520002501 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (219537554379 / 10000000000000 : ℝ))
      (E := (cell13185 ⟨33, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82930520002501 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (219537554379 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_34 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (828964323781 / 1000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195379549847 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨34, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (828964323781 / 1000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195379549847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_35 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (1035779605809 / 1250000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097691794373 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨35, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (1035779605809 / 1250000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097691794373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_36 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82828328231813 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195387602117 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨36, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82828328231813 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195387602117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_37 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82794311648983 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097695795001 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨37, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82794311648983 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097695795001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_38 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82760318685991 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195395610963 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨38, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82760318685991 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195395610963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_39 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82726349312749 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439079932933 / 20000000000000 : ℝ))
      (E := (cell13185 ⟨39, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82726349312749 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439079932933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13186_20 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (41687908549459 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195213025231 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨20, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (41687908549459 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195213025231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_21 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83341418385327 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548804256463 / 25000000000000 : ℝ))
      (E := (cell13186 ⟨21, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83341418385327 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548804256463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_22 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (41653521897197 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548805273241 / 25000000000000 : ℝ))
      (E := (cell13186 ⟨22, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (41653521897197 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548805273241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_23 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83272693293473 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548806263691 / 25000000000000 : ℝ))
      (E := (cell13186 ⟨23, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83272693293473 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548806263691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_24 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (20809591712521 / 25000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097614544721 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨24, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (20809591712521 / 25000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097614544721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_25 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (41602032215957 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (219523314147 / 10000000000000 : ℝ))
      (E := (cell13186 ⟨25, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (41602032215957 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (219523314147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_26 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (41584893003407 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097618577497 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨26, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (41584893003407 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097618577497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_27 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83135531542801 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (13720257077 / 625000000000 : ℝ))
      (E := (cell13186 ⟨27, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83135531542801 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (13720257077 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_28 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (10387662626007 / 12500000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548811298137 / 25000000000000 : ℝ))
      (E := (cell13186 ⟨28, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (10387662626007 / 12500000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548811298137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_29 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (83067094370919 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (109762458103 / 5000000000000 : ℝ))
      (E := (cell13186 ⟨29, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (83067094370919 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (109762458103 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_30 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (16606582319979 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097626609039 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨30, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (16606582319979 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097626609039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_31 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82998752663647 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195257244969 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨31, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82998752663647 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195257244969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_32 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82964617530999 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097630621947 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨32, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82964617530999 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097630621947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_33 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (20732626542733 / 25000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195265274417 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨33, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (20732626542733 / 25000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195265274417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_34 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (16579283710517 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195269278667 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨34, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (16579283710517 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195269278667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_35 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (16572470929051 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097636657901 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨35, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (16572470929051 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097636657901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_36 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (10353539302299 / 12500000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097638663729 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨36, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (10353539302299 / 12500000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097638663729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_37 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82794297841601 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097640656837 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨37, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82794297841601 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097640656837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_38 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82760304884643 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548821333253 / 25000000000000 : ℝ))
      (E := (cell13186 ⟨38, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82760304884643 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548821333253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_39 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82726335517429 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195289385139 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨39, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82726335517429 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195289385139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13187_20 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83375803190291 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195102779413 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨20, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83375803190291 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195102779413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_21 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (4167070224141 / 5000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195106777623 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨21, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (4167070224141 / 5000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195106777623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_22 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83307029898003 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097555391999 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨22, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83307029898003 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097555391999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_23 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83272679403191 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (548778700463 / 25000000000000 : ℝ))
      (E := (cell13187 ⟨23, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83272679403191 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (548778700463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_24 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83238352965907 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195118834259 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨24, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83238352965907 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195118834259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_25 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (20801012638459 / 25000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195122825621 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨25, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (20801012638459 / 25000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195122825621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_26 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (8316977213483 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (137195430963 / 6250000000000 : ℝ))
      (E := (cell13187 ⟨26, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (8316977213483 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (137195430963 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_27 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83135517676907 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195130870601 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨27, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83135517676907 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195130870601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_28 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (16620257429649 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (274391866093 / 12500000000000 : ℝ))
      (E := (cell13187 ⟨28, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (16620257429649 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (274391866093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_29 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (83067080517187 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195138896217 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨29, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (83067080517187 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195138896217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_30 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (20758224438059 / 25000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (548785737561 / 25000000000000 : ℝ))
      (E := (cell13187 ⟨30, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (20758224438059 / 25000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (548785737561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_31 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82998738822057 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (548786743797 / 25000000000000 : ℝ))
      (E := (cell13187 ⟨31, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82998738822057 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (548786743797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_32 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (5185287730967 / 6250000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195150972213 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨32, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (5185287730967 / 6250000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195150972213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_33 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82930492341463 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195155000883 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨33, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82930492341463 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195155000883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_34 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (8289640472917 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (87806360133 / 4000000000000 : ℝ))
      (E := (cell13187 ⟨34, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (8289640472917 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (87806360133 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_35 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (5178896301743 / 6250000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (21951630387 / 1000000000000 : ℝ))
      (E := (cell13187 ⟨35, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (5178896301743 / 6250000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (21951630387 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_36 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (20707075151767 / 25000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195167048641 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨36, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (20707075151767 / 25000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195167048641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_37 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (16558856807263 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (274396386489 / 12500000000000 : ℝ))
      (E := (cell13187 ⟨37, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (16558856807263 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (274396386489 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_38 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (8276029108539 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195175109651 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨38, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (8276029108539 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195175109651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_39 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (16545264344841 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439035820291 / 20000000000000 : ℝ))
      (E := (cell13187 ⟨39, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (16545264344841 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439035820291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13188_20 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (1302746707559 / 1562500000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (137187033089 / 6250000000000 : ℝ))
      (E := (cell13188 ⟨20, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (1302746707559 / 1562500000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (137187033089 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_21 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (10417673822803 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (87799861009 / 4000000000000 : ℝ))
      (E := (cell13188 ⟨21, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (10417673822803 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (87799861009 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_22 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83307016003721 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (274375073451 / 12500000000000 : ℝ))
      (E := (cell13188 ⟨22, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83307016003721 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (274375073451 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_23 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83272665515019 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195004603167 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨23, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83272665515019 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195004603167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_24 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41619169541919 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195008574909 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨24, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41619169541919 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195008574909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_25 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (16640807335573 / 20000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (219501262249 / 10000000000000 : ℝ))
      (E := (cell13188 ⟨25, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (16640807335573 / 20000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (219501262249 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_26 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83169758264953 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195016631657 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨26, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83169758264953 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195016631657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_27 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41567751906559 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (274377582901 / 12500000000000 : ℝ))
      (E := (cell13188 ⟨27, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41567751906559 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (274377582901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_28 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (83101273290539 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097512330389 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨28, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (83101273290539 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097512330389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_29 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41533533332779 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195028684749 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨29, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41533533332779 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195028684749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_30 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (2075822097667 / 2500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (274379084781 / 12500000000000 : ℝ))
      (E := (cell13188 ⟨30, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (2075822097667 / 2500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (274379084781 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_31 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (10374840622821 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195036701247 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨31, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (10374840622821 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195036701247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_32 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41482294931023 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097520377489 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨32, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41482294931023 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097520377489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_33 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (16586095702819 / 20000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195044723189 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨33, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (16586095702819 / 20000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195044723189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_34 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41448195453927 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195048782477 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨34, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41448195453927 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195048782477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_35 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82862327012619 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (6859539867 / 312500000000 : ℝ))
      (E := (cell13188 ⟨35, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82862327012619 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (6859539867 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_36 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82828286797841 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195056824367 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨36, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82828286797841 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195056824367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_37 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41397135116563 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (219506080727 / 10000000000000 : ℝ))
      (E := (cell13188 ⟨37, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41397135116563 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (219506080727 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_38 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82760277288233 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (548766205847 / 25000000000000 : ℝ))
      (E := (cell13188 ⟨38, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82760277288233 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (548766205847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_39 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (3309052317323 / 4000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195068872387 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨39, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (3309052317323 / 4000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195068872387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13189_20 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83375775379373 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194882333591 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨20, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83375775379373 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194882333591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_21 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83341376684139 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (438977265401 / 20000000000000 : ℝ))
      (E := (cell13189 ⟨21, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83341376684139 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (438977265401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_22 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83307002111549 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097445164339 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨22, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83307002111549 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097445164339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_23 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (16654530325791 / 20000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194894341921 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨23, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (16654530325791 / 20000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194894341921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_24 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83238325203877 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (548724592453 / 25000000000000 : ℝ))
      (E := (cell13189 ⟨24, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83238325203877 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (548724592453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_25 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41602011402001 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274362801899 / 12500000000000 : ℝ))
      (E := (cell13189 ⟨25, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41602011402001 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274362801899 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_26 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41584872198591 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097453211103 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨26, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41584872198591 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097453211103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_27 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83135489951433 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (548727612913 / 25000000000000 : ℝ))
      (E := (cell13189 ⟨27, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83135489951433 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (548727612913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_28 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (10387657429367 / 12500000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194914447161 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨28, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (10387657429367 / 12500000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194914447161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_29 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83067052816033 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194918469117 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨29, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83067052816033 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194918469117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_30 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (83032870063227 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274365307581 / 12500000000000 : ℝ))
      (E := (cell13189 ⟨30, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (83032870063227 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274365307581 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_31 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82998711145181 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194926481727 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨31, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82998711145181 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194926481727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_32 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (4051004689 / 4882812500 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (137183158349 / 6250000000000 : ℝ))
      (E := (cell13189 ⟨32, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (4051004689 / 4882812500 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (137183158349 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_33 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41465232344413 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097467249983 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨33, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41465232344413 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097467249983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_34 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (20724094272159 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194938557473 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨34, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (20724094272159 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194938557473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_35 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82862313199447 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (34295977959 / 1562500000000 : ℝ))
      (E := (cell13189 ⟨35, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82862313199447 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (34295977959 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_36 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82828272990711 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097473297969 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨36, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82828272990711 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097473297969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_37 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (2587320513501 / 3125000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194950577197 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨37, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (2587320513501 / 3125000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194950577197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_38 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82760263493171 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097477295859 / 50000000000000 : ℝ))
      (E := (cell13189 ⟨38, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82760263493171 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (1097477295859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_39 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82726294144039 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194958639167 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨39, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82726294144039 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194958639167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13190_20 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (2084394036927 / 2500000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548693033397 / 25000000000000 : ℝ))
      (E := (cell13190 ⟨20, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (2084394036927 / 2500000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548693033397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_21 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (20835340696991 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194776124617 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨21, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (20835340696991 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194776124617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_22 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41653494110743 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (137173757747 / 6250000000000 : ℝ))
      (E := (cell13190 ⟨22, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41653494110743 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (137173757747 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_23 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83272637744999 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194784134903 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨23, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83272637744999 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194784134903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_24 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83238311326023 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548697040137 / 25000000000000 : ℝ))
      (E := (cell13190 ⟨24, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83238311326023 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548697040137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_25 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (20801002233061 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (219479220373 / 10000000000000 : ℝ))
      (E := (cell13190 ⟨25, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (20801002233061 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (219479220373 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_26 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (20792432632879 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194796208591 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨26, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (20792432632879 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194796208591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_27 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83135476091853 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194800235931 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨27, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83135476091853 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194800235931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_28 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (83101245581437 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194804229381 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨28, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (83101245581437 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194804229381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_29 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (8306703896861 / 10000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548702062331 / 25000000000000 : ℝ))
      (E := (cell13190 ⟨29, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (8306703896861 / 10000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548702062331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_30 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41516428110937 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194812297449 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨30, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41516428110937 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194812297449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_31 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (16599739461979 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194816316629 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨31, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (16599739461979 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194816316629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_32 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (16592912440299 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (219482030803 / 10000000000000 : ℝ))
      (E := (cell13190 ⟨32, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (16592912440299 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (219482030803 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_33 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (10366306358207 / 12500000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097412165607 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨33, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (10366306358207 / 12500000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097412165607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_34 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (20724090817879 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (219482832831 / 10000000000000 : ℝ))
      (E := (cell13190 ⟨34, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (20724090817879 / 25000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (219482832831 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_35 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82862299388373 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097416179239 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨35, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82862299388373 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097416179239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_36 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82828259185677 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194836363351 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨36, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82828259185677 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194836363351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_37 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41397121316517 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194840401691 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨37, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41397121316517 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194840401691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_38 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82760249700203 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (27435555183 / 1250000000000 : ℝ))
      (E := (cell13190 ⟨38, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82760249700203 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (27435555183 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_39 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82726280357097 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194848460561 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨39, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82726280357097 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194848460561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13191_20 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41687873788449 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097330964709 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨20, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41687873788449 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097330964709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_21 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83341348893899 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194665918063 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨21, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83341348893899 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194665918063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_22 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (20826743583383 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (274333746679 / 12500000000000 : ℝ))
      (E := (cell13191 ⟨22, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (20826743583383 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (274333746679 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_23 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83272623863151 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548668495529 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨23, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83272623863151 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548668495529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_24 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (3329531898011 / 4000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194678005541 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨24, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (3329531898011 / 4000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194678005541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_25 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83203995062593 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438936397621 / 20000000000000 : ℝ))
      (E := (cell13191 ⟨25, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83203995062593 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438936397621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_26 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41584858333977 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194686049281 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨26, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41584858333977 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194686049281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_27 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41567731117189 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194690016049 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨27, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41567731117189 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194690016049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_28 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41550615865021 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194694065953 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨28, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41550615865021 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194694065953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_29 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (83067025123289 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548674520977 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨29, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (83067025123289 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548674520977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_30 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (2594776324457 / 3125000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (219470207153 / 10000000000000 : ℝ))
      (E := (cell13191 ⟨30, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (2594776324457 / 3125000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (219470207153 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_31 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82998683476709 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (274338261099 / 12500000000000 : ℝ))
      (E := (cell13191 ⟨31, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82998683476709 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (274338261099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_32 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (2592642136699 / 3125000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097355068463 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨32, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (2592642136699 / 3125000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097355068463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_33 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (10366304630573 / 12500000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194714158307 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨33, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (10366304630573 / 12500000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194714158307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_34 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41448174728247 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097359076823 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨34, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41448174728247 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097359076823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_35 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (20715571394849 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194722182103 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨35, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (20715571394849 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194722182103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_36 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82828245382739 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (68585193291 / 3125000000000 : ℝ))
      (E := (cell13191 ⟨36, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82828245382739 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (68585193291 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_37 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (8279422883613 / 10000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097365111017 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨37, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (8279422883613 / 10000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097365111017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_38 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82760235909329 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (219473423341 / 10000000000000 : ℝ))
      (E := (cell13191 ⟨38, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82760235909329 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (219473423341 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_39 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82726266572247 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194738277807 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨39, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82726266572247 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194738277807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13192_20 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41687866839413 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (438910355881 / 20000000000000 : ℝ))
      (E := (cell13192 ⟨20, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41687866839413 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (438910355881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_21 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41670667500971 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194555765691 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨21, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41670667500971 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194555765691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_22 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41653480223843 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097279909373 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨22, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41653480223843 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097279909373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_23 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (8327260998341 / 10000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548640956291 / 25000000000000 : ℝ))
      (E := (cell13192 ⟨23, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (8327260998341 / 10000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548640956291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_24 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (16647656715327 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194567846367 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨24, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (16647656715327 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194567846367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_25 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41601990597523 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194571826759 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨25, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41601990597523 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194571826759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_26 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41584851403249 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194575885807 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨26, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41584851403249 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194575885807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_27 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (16627089675801 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (438915970099 / 20000000000000 : ℝ))
      (E := (cell13192 ⟨27, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (16627089675801 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (438915970099 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_28 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (83101217880749 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548645974591 / 25000000000000 : ℝ))
      (E := (cell13192 ⟨28, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (83101217880749 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548645974591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_29 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (8306701128007 / 10000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548646978583 / 25000000000000 : ℝ))
      (E := (cell13192 ⟨29, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (8306701128007 / 10000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548646978583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_30 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41516414272737 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194591958571 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨30, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41516414272737 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194591958571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_31 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82998669645623 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097297986981 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨31, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82998669645623 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097297986981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_32 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82964534549341 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (34290624401 / 1562500000000 : ℝ))
      (E := (cell13192 ⟨32, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82964534549341 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (34290624401 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_33 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (8293042322561 / 10000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194603981243 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨33, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (8293042322561 / 10000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194603981243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_34 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82896335643569 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097303987413 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨34, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82896335643569 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097303987413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_35 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41431135886257 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194612001573 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨35, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41431135886257 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194612001573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_36 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (10353528947737 / 12500000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194616061819 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨36, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (10353528947737 / 12500000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194616061819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_37 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82794215041321 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194620038223 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨37, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82794215041321 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194620038223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_38 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (20690055530137 / 25000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194624048029 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨38, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (20690055530137 / 25000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194624048029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_39 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (8272625278949 / 10000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194628090901 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨39, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (8272625278949 / 10000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194628090901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13193_20 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83375719782863 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548610406307 / 25000000000000 : ℝ))
      (E := (cell13193 ⟨20, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83375719782863 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548610406307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_21 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (16668264222419 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194445609153 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨21, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (16668264222419 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194445609153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_22 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (20826736640987 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194449659897 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨22, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (20826736640987 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194449659897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_23 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (5204537256611 / 6250000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (137153354003 / 6250000000000 : ℝ))
      (E := (cell13193 ⟨23, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (5204537256611 / 6250000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (137153354003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_24 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (83238269705099 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194457683033 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨24, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (83238269705099 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194457683033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_25 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (16640793465921 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097230859847 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨25, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (16640793465921 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097230859847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_26 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (16633937789429 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097232859087 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨26, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (16633937789429 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097232859087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_27 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (10391929315717 / 12500000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (219446973927 / 10000000000000 : ℝ))
      (E := (cell13193 ⟨27, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (10391929315717 / 12500000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (219446973927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_28 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41550602016779 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194473726617 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨28, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41550602016779 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194473726617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_29 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (10383374679869 / 12500000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097238870299 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨29, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (10383374679869 / 12500000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097238870299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_30 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (10379101838803 / 12500000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194481782897 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨30, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (10379101838803 / 12500000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194481782897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_31 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (20749663954159 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194485796393 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨31, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (20749663954159 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194485796393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_32 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (20741130181603 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097244920427 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨32, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (20741130181603 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097244920427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_33 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41465204704367 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097246929327 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨33, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41465204704367 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097246929327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_34 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82896321832741 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438899570101 / 20000000000000 : ℝ))
      (E := (cell13193 ⟨34, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82896321832741 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438899570101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_35 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (5178891122983 / 6250000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (137156367223 / 6250000000000 : ℝ))
      (E := (cell13193 ⟨35, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (5178891122983 / 6250000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (137156367223 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_36 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (20707054445787 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194505875473 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨36, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (20707054445787 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194505875473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_37 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (16558840249721 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097254954493 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨37, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (16558840249721 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097254954493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_38 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (4138010416693 / 5000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548628479311 / 25000000000000 : ℝ))
      (E := (cell13193 ⟨38, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (4138010416693 / 5000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548628479311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_39 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (3309049560353 / 4000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438903591723 / 20000000000000 : ℝ))
      (E := (cell13193 ⟨39, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (3309049560353 / 4000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438903591723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13194_20 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (8337570588901 / 10000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438866293377 / 20000000000000 : ℝ))
      (E := (cell13194 ⟨20, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (8337570588901 / 10000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438866293377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_21 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (16668261444871 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194335506801 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨21, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (16668261444871 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194335506801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_22 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83306932682317 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548584874221 / 25000000000000 : ℝ))
      (E := (cell13194 ⟨22, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83306932682317 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548584874221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_23 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (10409072778781 / 12500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097171778583 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨23, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (10409072778781 / 12500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097171778583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_24 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (8323825583567 / 10000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548586893489 / 25000000000000 : ℝ))
      (E := (cell13194 ⟨24, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (8323825583567 / 10000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548586893489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_25 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (20800988366567 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097175775013 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨25, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (20800988366567 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097175775013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_26 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (10396209386237 / 12500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097177802423 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨26, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (10396209386237 / 12500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097177802423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_27 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (83135420674569 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194359623887 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨27, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (83135420674569 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194359623887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_28 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (20775297547117 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (87774544369 / 4000000000000 : ℝ))
      (E := (cell13194 ⟨28, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (20775297547117 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (87774544369 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_29 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (16613396719987 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097183810621 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨29, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (16613396719987 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097183810621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_30 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41516400438737 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (17554973293 / 800000000000 : ℝ))
      (E := (cell13194 ⟨30, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41516400438737 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (17554973293 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_31 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (20749660497437 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548593918313 / 25000000000000 : ℝ))
      (E := (cell13194 ⟨31, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (20749660497437 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548593918313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_32 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82964506905581 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194379715889 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨32, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82964506905581 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194379715889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_33 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (16586079118791 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (274297966489 / 12500000000000 : ℝ))
      (E := (cell13194 ⟨33, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (16586079118791 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (274297966489 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_34 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (10362038503001 / 12500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (137149232627 / 6250000000000 : ℝ))
      (E := (cell13194 ⟨34, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (10362038503001 / 12500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (137149232627 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_35 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41431122082519 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194391745409 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨35, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41431122082519 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194391745409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_36 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41414101993247 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194395743677 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨36, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41414101993247 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194395743677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_37 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82794187457983 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097199887799 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨37, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82794187457983 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097199887799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_38 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (16552038909853 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (219440378231 / 10000000000000 : ℝ))
      (E := (cell13194 ⟨38, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (16552038909853 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (219440378231 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_39 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82726225230251 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097203911091 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨39, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82726225230251 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097203911091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13195_20 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16675138399453 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (137138835169 / 6250000000000 : ℝ))
      (E := (cell13195 ⟨20, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16675138399453 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (137138835169 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_21 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (83341293338723 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194225400287 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨21, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (83341293338723 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194225400287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_22 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (10413364850349 / 12500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438845889291 / 20000000000000 : ℝ))
      (E := (cell13195 ⟨22, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (10413364850349 / 12500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438845889291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_23 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41636284178413 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548558361531 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨23, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41636284178413 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548558361531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_24 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16647648393669 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194237460719 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨24, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16647648393669 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194237460719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_25 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16640787921007 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548560373271 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨25, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16640787921007 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548560373271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_26 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (332678644939 / 400000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1714254287 / 78125000000 : ℝ))
      (E := (cell13195 ⟨26, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (332678644939 / 400000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1714254287 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_27 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16627081365101 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097124752173 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨27, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16627081365101 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097124752173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_28 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (2077529408637 / 2500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194253546189 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨28, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (2077529408637 / 2500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194253546189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_29 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41533484881509 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548564389067 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨29, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41533484881509 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548564389067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_30 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (83032787046623 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (10971307681 / 500000000000 : ℝ))
      (E := (cell13195 ⟨30, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (83032787046623 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (10971307681 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_31 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41499314082479 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (109713280227 / 5000000000000 : ℝ))
      (E := (cell13195 ⟨31, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41499314082479 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (109713280227 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_32 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82964493086847 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194269586771 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨32, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82964493086847 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194269586771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_33 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (10366297722659 / 12500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097136800509 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨33, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (10366297722659 / 12500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097136800509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_34 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82896294217371 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194277648061 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨34, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82896294217371 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194277648061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_35 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41431115182221 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097140834889 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨35, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41431115182221 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097140834889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_36 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41414095095967 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (17142856769 / 781250000000 : ℝ))
      (E := (cell13195 ⟨36, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41414095095967 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (17142856769 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_37 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41397086834727 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (137143106049 / 6250000000000 : ℝ))
      (E := (cell13195 ⟨37, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41397086834727 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (137143106049 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_38 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82760180766761 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (274286712747 / 12500000000000 : ℝ))
      (E := (cell13195 ⟨38, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82760180766761 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (274286712747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_39 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82726211453769 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194297740371 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨39, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82726211453769 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194297740371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13196_20 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (20843919526907 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (438822262537 / 20000000000000 : ℝ))
      (E := (cell13196 ⟨20, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (20843919526907 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (438822262537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_21 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41670639727599 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097057673979 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨21, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41670639727599 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097057673979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_22 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41653452462687 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194119333491 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨22, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41653452462687 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194119333491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_23 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83272554485509 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (54853083273 / 2500000000000 : ℝ))
      (E := (cell13196 ⟨23, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83272554485509 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (54853083273 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_24 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (20809557025781 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097063671661 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨24, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (20809557025781 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097063671661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_25 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41601962872953 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194131373539 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨25, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41601962872953 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194131373539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_26 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41584823690853 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097067712091 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨26, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41584823690853 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097067712091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_27 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41567696489271 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097069719569 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨27, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41567696489271 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097069719569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_28 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83101162504593 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194143420483 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨28, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83101162504593 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194143420483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_29 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83066955928201 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194147428601 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨29, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83066955928201 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194147428601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_30 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (83032773217871 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097075732589 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨30, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (83032773217871 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097075732589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_31 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82998614342267 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (219415547309 / 10000000000000 : ℝ))
      (E := (cell13196 ⟨31, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82998614342267 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (219415547309 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_32 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82964479270211 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097079756053 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨32, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82964479270211 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097079756053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_33 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (16586073594137 / 20000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194163524601 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨33, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (16586073594137 / 20000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194163524601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_34 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (8289628041283 / 10000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097083784969 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨34, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (8289628041283 / 10000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097083784969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_35 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (4143110828297 / 5000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548542897499 / 25000000000000 : ℝ))
      (E := (cell13196 ⟨35, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (4143110828297 / 5000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548542897499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_36 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82828176399467 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548543896259 / 25000000000000 : ℝ))
      (E := (cell13196 ⟨36, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82828176399467 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548543896259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_37 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82794159883017 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097089806911 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨37, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82794159883017 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097089806911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_38 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82760166986349 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194183617493 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨38, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82760166986349 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194183617493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_39 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82726197679377 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097093827207 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨39, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82726197679377 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097093827207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13197_20 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83375664220099 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274250157313 / 12500000000000 : ℝ))
      (E := (cell13197 ⟨20, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83375664220099 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274250157313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_21 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83341265573779 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (13712532707 / 625000000000 : ℝ))
      (E := (cell13197 ⟨21, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83341265573779 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (13712532707 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_22 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83306891050061 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (109700463737 / 5000000000000 : ℝ))
      (E := (cell13197 ⟨22, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83306891050061 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (109700463737 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_23 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83272540616297 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194013269953 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨23, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83272540616297 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194013269953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_24 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83238214240007 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097008640093 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨24, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83238214240007 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097008640093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_25 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83203911888879 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194021308281 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨25, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83203911888879 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194021308281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_26 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (20792408382691 / 25000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194025356847 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨26, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (20792408382691 / 25000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194025356847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_27 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (1039192239171 / 1250000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194029369773 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨27, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (1039192239171 / 1250000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194029369773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_28 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16620229733161 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (137127084321 / 6250000000000 : ℝ))
      (E := (cell13197 ⟨28, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16620229733161 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (137127084321 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_29 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (83066942095483 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194037413853 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨29, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (83066942095483 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194037413853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_30 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (41516379695609 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097020695001 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨30, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (41516379695609 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097020695001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_31 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (10374825065209 / 12500000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097022727327 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨31, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (10374825065209 / 12500000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097022727327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_32 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82964465455671 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194049433289 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨32, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82964465455671 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194049433289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_33 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (41465177081097 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194053444033 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨33, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (41465177081097 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194053444033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_34 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82896266610383 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (438811497533 / 20000000000000 : ℝ))
      (E := (cell13197 ⟨34, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82896266610383 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (438811497533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_35 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (20715550692383 / 25000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (137128844129 / 6250000000000 : ℝ))
      (E := (cell13197 ⟨35, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (20715550692383 / 25000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (137128844129 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_36 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82828162609093 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548516374873 / 25000000000000 : ℝ))
      (E := (cell13197 ⟨36, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82828162609093 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548516374873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_37 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (5174634131167 / 6250000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274258690839 / 12500000000000 : ℝ))
      (E := (cell13197 ⟨37, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (5174634131167 / 6250000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274258690839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_38 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82760153208029 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194073587609 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨38, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82760153208029 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194073587609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_39 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (3309047356283 / 4000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219407756431 / 10000000000000 : ℝ))
      (E := (cell13197 ⟨39, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (3309047356283 / 4000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219407756431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13198_20 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83375650334677 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193891200163 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨20, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83375650334677 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193891200163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_21 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83341251694467 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (109694761541 / 5000000000000 : ℝ))
      (E := (cell13198 ⟨21, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83341251694467 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (109694761541 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_22 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41653438588427 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193899211829 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨22, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41653438588427 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193899211829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_23 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (83272526749189 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (274237907903 / 12500000000000 : ℝ))
      (E := (cell13198 ⟨23, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (83272526749189 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (274237907903 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_24 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41619100189497 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193907271311 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨24, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41619100189497 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193907271311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_25 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (16640779606791 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (548477824327 / 25000000000000 : ℝ))
      (E := (cell13198 ⟨25, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (16640779606791 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (548477824327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_26 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (20792404920481 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193915285357 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨26, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (20792404920481 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193915285357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_27 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41567682645459 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096959648127 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨27, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41567682645459 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096959648127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_28 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41550567414559 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096961666073 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨28, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41550567414559 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096961666073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_29 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (2595841508277 / 3125000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438785467283 / 20000000000000 : ℝ))
      (E := (cell13198 ⟨29, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (2595841508277 / 3125000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438785467283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_30 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41516372783331 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438786273847 / 20000000000000 : ℝ))
      (E := (cell13198 ⟨30, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41516372783331 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438786273847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_31 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (3319943468127 / 4000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (548483843371 / 25000000000000 : ℝ))
      (E := (cell13198 ⟨31, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (3319943468127 / 4000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (548483843371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_32 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82964451643227 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (68560606529 / 3125000000000 : ℝ))
      (E := (cell13198 ⟨32, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82964451643227 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (68560606529 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_33 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82930340355799 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438788683589 / 20000000000000 : ℝ))
      (E := (cell13198 ⟨33, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82930340355799 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438788683589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_34 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (8289625281003 / 10000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193947459897 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨34, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (8289625281003 / 10000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193947459897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_35 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41431094487609 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193951476661 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨35, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41431094487609 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193951476661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_36 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (20707037205203 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193955468501 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨36, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (20707037205203 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193955468501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_37 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82794132316419 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193959494179 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨37, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82794132316419 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193959494179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_38 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41380069715899 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438792698967 / 20000000000000 : ℝ))
      (E := (cell13198 ⟨38, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41380069715899 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438792698967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_39 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82726170136863 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193967528833 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨39, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82726170136863 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193967528833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13199_20 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83375636451361 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548445298997 / 25000000000000 : ℝ))
      (E := (cell13199 ⟨20, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83375636451361 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548445298997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_21 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83341237817261 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548446291503 / 25000000000000 : ℝ))
      (E := (cell13199 ⟨21, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83341237817261 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548446291503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_22 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (10413357913219 / 12500000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193789203133 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨22, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (10413357913219 / 12500000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193789203133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_23 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41636256442093 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193793193941 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨23, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41636256442093 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193793193941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_24 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (20809546630021 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193797258281 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨24, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (20809546630021 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193797258281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_25 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83203884181133 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193801223737 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨25, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83203884181133 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193801223737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_26 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (16633921167037 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096902634089 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨26, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (16633921167037 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096902634089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_27 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83135351450257 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193809277071 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨27, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83135351450257 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193809277071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_28 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (83101120994529 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096906655503 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨28, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (83101120994529 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096906655503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_29 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (10383364304543 / 12500000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096908656681 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨29, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (10383364304543 / 12500000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096908656681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_30 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (20758182936051 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193821344317 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨30, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (20758182936051 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193821344317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_31 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41499286443387 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548456336687 / 25000000000000 : ℝ))
      (E := (cell13199 ⟨31, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41499286443387 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548456336687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_32 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41482218916439 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (109691469021 / 5000000000000 : ℝ))
      (E := (cell13199 ⟨32, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41482218916439 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (109691469021 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_33 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82930326551497 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219383338771 / 10000000000000 : ℝ))
      (E := (cell13199 ⟨33, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82930326551497 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219383338771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_34 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82896239011771 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096918713991 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨34, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82896239011771 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096918713991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_35 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (20715543795749 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193841443113 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨35, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (20715543795749 / 25000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193841443113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_36 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41414067517311 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096922716683 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨36, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41414067517311 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096922716683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_37 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (1293658102129 / 1562500000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193849457503 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨37, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (1293658102129 / 1562500000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193849457503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_38 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41380062828829 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219385351541 / 10000000000000 : ℝ))
      (E := (cell13199 ⟨38, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41380062828829 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219385351541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_39 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (4136307818437 / 5000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193857489213 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨39, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (4136307818437 / 5000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193857489213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

end BstLean.Part268
