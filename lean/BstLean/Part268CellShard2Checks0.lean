import BstLean.Part268CellShard2Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12400_0 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (84080639151807 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145072091821 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨0, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (84080639151807 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145072091821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_1 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (21011391586071 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458029642761 / 20000000000000 : ℝ))
      (E := (cell12400 ⟨1, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (21011391586071 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458029642761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_2 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (42005259304781 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145076076969 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨2, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (42005259304781 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145076076969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_3 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (5248468494427 / 6250000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286269523367 / 12500000000000 : ℝ))
      (E := (cell12400 ⟨3, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (5248468494427 / 6250000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286269523367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_4 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (2098512455287 / 2500000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (55912113 / 2441406250 : ℝ))
      (E := (cell12400 ⟨4, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (2098512455287 / 2500000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (55912113 / 2441406250 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_5 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (16781105095017 / 20000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290164163189 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨5, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (16781105095017 / 20000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290164163189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_6 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (4193528883271 / 5000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290168181851 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨6, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (4193528883271 / 5000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290168181851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_7 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41917827373223 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145086077453 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨7, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41917827373223 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145086077453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_8 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41900378341157 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145088074189 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨8, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41900378341157 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145088074189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_9 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (20941470859341 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286272521267 / 12500000000000 : ℝ))
      (E := (cell12400 ⟨9, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (20941470859341 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286272521267 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_10 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (83731034976123 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145092055887 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨10, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (83731034976123 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145092055887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_11 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (10462026407913 / 12500000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (18321505237 / 800000000000 : ℝ))
      (E := (cell12400 ⟨11, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (10462026407913 / 12500000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (18321505237 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_12 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (20915353065951 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458038426339 / 20000000000000 : ℝ))
      (E := (cell12400 ⟨12, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (20915353065951 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458038426339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_13 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41813318971351 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290196107791 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨13, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41813318971351 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290196107791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_14 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41795944132631 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290200089459 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨14, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41795944132631 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290200089459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_15 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41778581598463 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286275517641 / 12500000000000 : ℝ))
      (E := (cell12400 ⟨15, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41778581598463 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286275517641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_16 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (83522462703319 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458041618891 / 20000000000000 : ℝ))
      (E := (cell12400 ⟨16, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (83522462703319 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458041618891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_17 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (83487786750243 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145106064819 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨17, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (83487786750243 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145106064819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_18 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (20863283825919 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (572554019427 / 25000000000000 : ℝ))
      (E := (cell12400 ⟨18, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (20863283825919 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (572554019427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_19 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (5213656770611 / 6250000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (143138757407 / 6250000000000 : ℝ))
      (E := (cell12400 ⟨19, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (5213656770611 / 6250000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (143138757407 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12401_0 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (21020155820477 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290007858583 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨0, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (21020155820477 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290007858583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_1 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (84045550806481 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290011836259 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨1, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (84045550806481 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290011836259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_2 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (84010503403383 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (143125990019 / 6250000000000 : ℝ))
      (E := (cell12401 ⟨2, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (84010503403383 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (143125990019 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_3 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41987740517903 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572504955589 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨3, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41987740517903 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572504955589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_4 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83940483667139 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (143126486973 / 6250000000000 : ℝ))
      (E := (cell12401 ⟨4, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83940483667139 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (143126486973 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_5 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41952755630481 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145013907367 / 50000000000000 : ℝ))
      (E := (cell12401 ⟨5, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41952755630481 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145013907367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_6 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83870563781047 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290031784723 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨6, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83870563781047 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290031784723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_7 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41917820595679 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572508956433 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨7, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41917820595679 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572508956433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_8 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41900371728023 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290039772057 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨8, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41900371728023 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290039772057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_9 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (20941467634863 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290043805399 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨9, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (20941467634863 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290043805399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_10 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (16746204481221 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290047759403 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨10, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (16746204481221 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290047759403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_11 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83696199020717 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290051757369 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨11, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83696199020717 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290051757369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_12 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83661400348187 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290055748349 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨12, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83661400348187 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290055748349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_13 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (20906656588399 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290059739137 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨13, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (20906656588399 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290059739137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_14 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83591877002207 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145031868139 / 50000000000000 : ℝ))
      (E := (cell12401 ⟨14, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83591877002207 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145031868139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_15 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41778576129733 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290067746067 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨15, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41778576129733 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290067746067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_16 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (20880613022749 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572517943639 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨16, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (20880613022749 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572517943639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_17 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (417438882313 / 500000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572518942343 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨17, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (417438882313 / 500000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572518942343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_18 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83453125340259 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (458015947201 / 20000000000000 : ℝ))
      (E := (cell12401 ⟨18, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83453125340259 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (458015947201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_19 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (8341849869013 / 10000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572520934481 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨19, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (8341849869013 / 10000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572520934481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12402_0 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (84080607414573 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (5724678821 / 250000000000 : ℝ))
      (E := (cell12402 ⟨0, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (84080607414573 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (5724678821 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_1 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (42022767635599 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144937755719 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨1, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (42022767635599 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144937755719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_2 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (84010488199683 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144939760817 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨2, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (84010488199683 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144939760817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_3 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83975466163219 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289883510629 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨3, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83975466163219 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289883510629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_4 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (20985117281299 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289887545449 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨4, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (20985117281299 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289887545449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_5 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (16781099409839 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144945759633 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨5, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (16781099409839 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144945759633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_6 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (8387054989899 / 10000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144947749283 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨6, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (8387054989899 / 10000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144947749283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_7 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (5239726727409 / 6250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572474872933 / 25000000000000 : ℝ))
      (E := (cell12402 ⟨7, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (5239726727409 / 6250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572474872933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_8 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83800730232011 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144951753443 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨8, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83800730232011 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144951753443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_9 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (20941464410933 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289907493909 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨9, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (20941464410933 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289907493909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_10 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83731009838237 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144955730173 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨10, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83731009838237 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144955730173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_11 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (1046202334753 / 1250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (286239433941 / 12500000000000 : ℝ))
      (E := (cell12402 ⟨11, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (1046202334753 / 1250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (286239433941 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_12 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (1045767355433 / 1250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144959738253 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨12, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (1045767355433 / 1250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144959738253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_13 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83626614766519 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (91596939283 / 4000000000000 : ℝ))
      (E := (cell12402 ⟨13, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83626614766519 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (91596939283 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_14 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (41795932870571 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (286240936847 / 12500000000000 : ℝ))
      (E := (cell12402 ⟨14, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (41795932870571 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (286240936847 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_15 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (41778570661977 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289931462777 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨15, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (41778570661977 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289931462777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_16 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (4176122074029 / 5000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289935450209 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨16, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (4176122074029 / 5000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289935450209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_17 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (3339510647073 / 4000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (18319515703 / 800000000000 : ℝ))
      (E := (cell12402 ⟨17, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (3339510647073 / 4000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (18319515703 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_18 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (8345311537867 / 10000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (457988689627 / 20000000000000 : ℝ))
      (E := (cell12402 ⟨18, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (8345311537867 / 10000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (457988689627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_19 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (5213655565767 / 6250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289947469459 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨19, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (5213655565767 / 6250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289947469459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12403_0 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (84080591549799 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289735308657 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨0, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (84080591549799 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289735308657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_1 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (84045519738437 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289739297143 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨1, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (84045519738437 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289739297143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_2 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (42005236499231 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144871656791 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨2, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (42005236499231 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144871656791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_3 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (8397545129307 / 10000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (228974730961 / 10000000000000 : ℝ))
      (E := (cell12403 ⟨3, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (8397545129307 / 10000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (228974730961 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_4 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (1678809091713 / 2000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (114487564719 / 5000000000000 : ℝ))
      (E := (cell12403 ⟨4, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (1678809091713 / 2000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (114487564719 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_5 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (10488185354973 / 12500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144877638393 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨5, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (10488185354973 / 12500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144877638393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_6 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83870536019247 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286219908183 / 12500000000000 : ℝ))
      (E := (cell12403 ⟨6, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83870536019247 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286219908183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_7 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (20958903522001 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457952653759 / 20000000000000 : ℝ))
      (E := (cell12403 ⟨7, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (20958903522001 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457952653759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_8 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (2618772406569 / 3125000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457953447387 / 20000000000000 : ℝ))
      (E := (cell12403 ⟨8, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (2618772406569 / 3125000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457953447387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_9 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (20941461187551 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289771235671 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨9, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (20941461187551 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289771235671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_10 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83730997272521 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289775272619 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨10, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83730997272521 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289775272619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_11 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (41848087270937 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (572444809767 / 25000000000000 : ℝ))
      (E := (cell12403 ⟨11, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (41848087270937 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (572444809767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_12 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83661376523163 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289783258111 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨12, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83661376523163 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289783258111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_13 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83626603181471 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144893610221 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨13, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83626603181471 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144893610221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_14 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (16718370896413 / 20000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144895624373 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨14, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (16718370896413 / 20000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144895624373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_15 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (8355713039039 / 10000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286224404141 / 12500000000000 : ℝ))
      (E := (cell12403 ⟨15, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (8355713039039 / 10000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286224404141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_16 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (10440303859009 / 12500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144899618861 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨16, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (10440303859009 / 12500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144899618861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_17 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83487755892917 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (45796064203 / 2000000000000 : ℝ))
      (E := (cell12403 ⟨17, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83487755892917 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (45796064203 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_18 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (41726552709453 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286225901763 / 12500000000000 : ℝ))
      (E := (cell12403 ⟨18, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (41726552709453 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286225901763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_19 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (417092397081 / 500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (8944574987 / 390625000000 : ℝ))
      (E := (cell12403 ⟨19, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (417092397081 / 500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (8944574987 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12404_0 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (42040287843793 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (91583965663 / 4000000000000 : ℝ))
      (E := (cell12404 ⟨0, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (42040287843793 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (91583965663 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_1 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (16809100841639 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (286200391947 / 12500000000000 : ℝ))
      (E := (cell12404 ⟨1, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (16809100841639 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (286200391947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_2 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (84010457799721 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (143100443781 / 6250000000000 : ℝ))
      (E := (cell12404 ⟨2, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (84010457799721 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (143100443781 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_3 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (83975436425359 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289611103599 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨3, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (83975436425359 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289611103599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_4 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (167880880097 / 200000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457923019247 / 20000000000000 : ℝ))
      (E := (cell12404 ⟨4, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (167880880097 / 200000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457923019247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_5 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (10488183579091 / 12500000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (35775298239 / 1562500000000 : ℝ))
      (E := (cell12404 ⟨5, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (10488183579091 / 12500000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (35775298239 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_6 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41935261070909 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144811542709 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨6, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41935261070909 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144811542709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_7 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (10479450067467 / 12500000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289627098979 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨7, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (10479450067467 / 12500000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289627098979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_8 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41900351895319 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457926215627 / 20000000000000 : ℝ))
      (E := (cell12404 ⟨8, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41900351895319 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457926215627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_9 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (20941457964717 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289635088673 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨9, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (20941457964717 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289635088673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_10 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (16746196941791 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457927816039 / 20000000000000 : ℝ))
      (E := (cell12404 ⟨10, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (16746196941791 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457927816039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_11 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (83696162305617 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289643059991 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨11, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (83696162305617 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289643059991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_12 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (16732272922751 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289647093163 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨12, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (16732272922751 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289647093163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_13 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (20906647899613 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572412767601 / 25000000000000 : ℝ))
      (E := (cell12404 ⟨13, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (20906647899613 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572412767601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_14 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (3343673728999 / 4000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144827528147 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨14, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (3343673728999 / 4000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144827528147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_15 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (20889279864693 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572414764281 / 25000000000000 : ℝ))
      (E := (cell12404 ⟨15, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (20889279864693 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572414764281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_16 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (8352242026547 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (71551971217 / 3125000000000 : ℝ))
      (E := (cell12404 ⟨16, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (8352242026547 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (71551971217 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_17 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (667901964887 / 800000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (35776047959 / 1562500000000 : ℝ))
      (E := (cell12404 ⟨17, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (667901964887 / 800000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (35776047959 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_18 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (83453095460969 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (228967103391 / 10000000000000 : ℝ))
      (E := (cell12404 ⟨18, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (83453095460969 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (228967103391 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_19 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (83418469781913 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572418759003 / 25000000000000 : ℝ))
      (E := (cell12404 ⟨19, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (83418469781913 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572418759003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12405_0 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (16816111965587 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289463027153 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨0, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (16816111965587 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289463027153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_1 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (84045488680473 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457893405347 / 20000000000000 : ℝ))
      (E := (cell12405 ⟨1, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (84045488680473 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457893405347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_2 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (84010442603457 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289470998029 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨2, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (84010442603457 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289470998029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_3 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (20993855390021 / 25000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289475008297 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨3, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (20993855390021 / 25000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289475008297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_4 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41970212756873 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289479008887 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨4, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41970212756873 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289479008887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_5 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83905454428027 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572370752173 / 25000000000000 : ℝ))
      (E := (cell12405 ⟨5, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83905454428027 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572370752173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_6 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83870508266703 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289486958427 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨6, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83870508266703 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289486958427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_7 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41917793496871 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457898196457 / 20000000000000 : ℝ))
      (E := (cell12405 ⟨7, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41917793496871 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457898196457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_8 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (838006905733 / 1000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289494972523 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨8, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (838006905733 / 1000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289494972523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_9 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41882909484861 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289498994929 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨9, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41882909484861 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289498994929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_10 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83730972147539 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (228950294109 / 10000000000000 : ℝ))
      (E := (cell12405 ⟨10, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83730972147539 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (228950294109 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_11 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83696150071469 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144753467149 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨11, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83696150071469 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144753467149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_12 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (16732270541283 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (71547218177 / 3125000000000 : ℝ))
      (E := (cell12405 ⟨12, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (16732270541283 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (71547218177 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_13 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (4181329000873 / 5000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144757486941 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨13, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (4181329000873 / 5000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144757486941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_14 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83591831969873 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (114475945871 / 5000000000000 : ℝ))
      (E := (cell12405 ⟨14, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83591831969873 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (114475945871 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_15 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41778554264551 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289522934763 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨15, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41778554264551 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289522934763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_16 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (3340896386431 / 4000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (57238172893 / 2500000000000 : ℝ))
      (E := (cell12405 ⟨16, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (3340896386431 / 4000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (57238172893 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_17 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83487735330699 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289530924199 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨17, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83487735330699 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289530924199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_18 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83453085504857 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572383726889 / 25000000000000 : ℝ))
      (E := (cell12405 ⟨18, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83453085504857 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572383726889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_19 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (20854615037353 / 25000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (286192366157 / 12500000000000 : ℝ))
      (E := (cell12405 ⟨19, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (20854615037353 / 25000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (286192366157 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12406_0 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (84080543970843 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289326965397 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨0, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (84080543970843 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289326965397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_1 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (84045473155269 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144665485313 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨1, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (84045473155269 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144665485313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_2 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (84010427409671 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144667474179 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨2, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (84010427409671 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144667474179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_3 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41987703348623 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (71541842683 / 3125000000000 : ℝ))
      (E := (cell12406 ⟨3, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41987703348623 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (71541842683 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_4 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83940410981387 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144671458297 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨4, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83940410981387 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144671458297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_5 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83905440225679 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144673462593 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨5, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83905440225679 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144673462593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_6 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83870494393901 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457870188483 / 20000000000000 : ℝ))
      (E := (cell12406 ⟨6, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83870494393901 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457870188483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_7 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83835573450019 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144677459357 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨7, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83835573450019 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144677459357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_8 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (5237542334887 / 6250000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289358920101 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨8, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (5237542334887 / 6250000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289358920101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_9 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41882903041383 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (45787257929 / 2000000000000 : ℝ))
      (E := (cell12406 ⟨9, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41882903041383 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (45787257929 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_10 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (5233184974267 / 6250000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144683456659 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨10, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (5233184974267 / 6250000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144683456659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_11 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (8369613783943 / 10000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289370920027 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨11, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (8369613783943 / 10000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289370920027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_12 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83661340801143 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (71542966363 / 3125000000000 : ℝ))
      (E := (cell12406 ⟨12, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83661340801143 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (71542966363 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_13 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (2613330263703 / 3125000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289378872791 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨13, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (2613330263703 / 3125000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289378872791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_14 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41795910358379 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144691445117 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨14, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41795910358379 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144691445117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_15 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41778548800689 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (17885834891 / 781250000000 : ℝ))
      (E := (cell12406 ⟨15, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41778548800689 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (17885834891 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_16 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (16704479811597 / 20000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144695432181 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨16, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (16704479811597 / 20000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144695432181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_17 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (20871931263097 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (91575795639 / 4000000000000 : ℝ))
      (E := (cell12406 ⟨17, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (20871931263097 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (91575795639 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_18 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83453075550571 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144699446621 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨18, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83453075550571 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144699446621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_19 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (10427306314837 / 12500000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457880575281 / 20000000000000 : ℝ))
      (E := (cell12406 ⟨19, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (10427306314837 / 12500000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457880575281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12407_0 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (84080528116311 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (457838191261 / 20000000000000 : ℝ))
      (E := (cell12407 ⟨0, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (84080528116311 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (457838191261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_1 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (10505682204073 / 12500000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289194967247 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨1, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (10505682204073 / 12500000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289194967247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_2 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (42005206109181 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572299737871 / 25000000000000 : ℝ))
      (E := (cell12407 ⟨2, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (42005206109181 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572299737871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_3 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83975391836843 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289202976279 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨3, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83975391836843 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289202976279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_4 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41970198225711 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289206935103 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨4, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41970198225711 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289206935103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_5 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16781085205137 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289210952571 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨5, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16781085205137 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289210952571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_6 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83870480523411 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289214921543 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨6, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83870480523411 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289214921543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_7 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (10479444988571 / 12500000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289218908269 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨7, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (10479444988571 / 12500000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289218908269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_8 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16760132829063 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (228922292087 / 10000000000000 : ℝ))
      (E := (cell12407 ⟨8, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16760132829063 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (228922292087 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_9 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83765793197999 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144613454609 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨9, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83765793197999 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144613454609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_10 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41865473515577 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289230938869 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨10, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41865473515577 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289230938869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_11 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83696125609499 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289234901107 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨11, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83696125609499 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289234901107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_12 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41830664448969 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289238919021 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨12, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41830664448969 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289238919021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_13 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41813278430779 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144621441651 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨13, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41813278430779 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144621441651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_14 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (20897952366407 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289246916633 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨14, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (20897952366407 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289246916633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_15 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83557086675599 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289250909113 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨15, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83557086675599 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289250909113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_16 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83522388457101 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572313716679 / 25000000000000 : ℝ))
      (E := (cell12407 ⟨16, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83522388457101 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572313716679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_17 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41743857387971 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289258911529 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨17, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41743857387971 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289258911529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_18 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83453065598109 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289262874571 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨18, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83453065598109 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289262874571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_19 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (20854610222441 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144633438731 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨19, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (20854610222441 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144633438731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12408_0 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (42040256132169 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289055057659 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨0, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (42040256132169 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289055057659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_1 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (2626420066013 / 3125000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289059016601 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨1, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (2626420066013 / 3125000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289059016601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_2 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (84010397029529 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289063007409 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨2, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (84010397029529 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289063007409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_3 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (20993844244719 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457813407913 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨3, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (20993844244719 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457813407913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_4 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83940381923851 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144535503271 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨4, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83940381923851 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144535503271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_5 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (20976352957011 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (45781500659 / 2000000000000 : ℝ))
      (E := (cell12408 ⟨5, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (20976352957011 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (45781500659 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_6 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (81904752593 / 97656250000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289079011653 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨6, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (81904752593 / 97656250000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289079011653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_7 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83835546369387 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457816601779 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨7, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83835546369387 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457816601779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_8 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (20950162733667 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (228908697483 / 10000000000000 : ℝ))
      (E := (cell12408 ⟨8, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (20950162733667 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (228908697483 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_9 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41882890157711 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289090975243 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨9, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41882890157711 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289090975243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_10 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (16746186895237 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289094959727 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨10, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (16746186895237 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289094959727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_11 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (20924028345419 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289098993611 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨11, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (20924028345419 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289098993611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_12 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (52288323123 / 62500000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289102967879 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨12, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (52288323123 / 62500000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289102967879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_13 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83626545286647 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (228910694733 / 10000000000000 : ℝ))
      (E := (cell12408 ⟨13, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83626545286647 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (228910694733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_14 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (16718359643297 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144555469253 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨14, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (16718359643297 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144555469253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_15 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41778537875883 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144557473847 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨15, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41778537875883 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144557473847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_16 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41761188929061 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289118980939 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨16, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41761188929061 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289118980939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_17 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83487704501361 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289122927683 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨17, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83487704501361 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289122927683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_18 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83453055647471 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (286140870993 / 12500000000000 : ℝ))
      (E := (cell12408 ⟨18, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83453055647471 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (286140870993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_19 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (10427303907827 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289130932427 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨19, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (10427303907827 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289130932427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12409_0 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (84080496414923 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (143057447119 / 6250000000000 : ℝ))
      (E := (cell12409 ⟨0, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (84080496414923 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (143057447119 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_1 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (16809085318953 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288923176493 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨1, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (16809085318953 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288923176493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_2 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (84010381843171 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144463586981 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨2, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (84010381843171 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144463586981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_3 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (41987681061671 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (57223278893 / 2500000000000 : ℝ))
      (E := (cell12409 ⟨3, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (41987681061671 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (57223278893 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_4 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (41970183699337 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144467565457 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨4, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (41970183699337 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144467565457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_5 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (16781079526551 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (143058694277 / 6250000000000 : ℝ))
      (E := (cell12409 ⟨5, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (16781079526551 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (143058694277 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_6 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (16774090557873 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144471548453 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨6, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (16774090557873 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144471548453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_7 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83835532832477 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144473552353 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨7, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83835532832477 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144473552353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_8 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (67040510181 / 80000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144475569977 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨8, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (67040510181 / 80000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144475569977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_9 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83765767435033 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (4470615419 / 195312500000 : ℝ))
      (E := (cell12409 ⟨9, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83765767435033 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (4470615419 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_10 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83730921923363 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144479545963 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨10, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83730921923363 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144479545963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_11 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83696101155959 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (228896308147 / 10000000000000 : ℝ))
      (E := (cell12409 ⟨11, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83696101155959 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (228896308147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_12 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83661305097729 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (143060441887 / 6250000000000 : ℝ))
      (E := (cell12409 ⟨12, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83661305097729 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (143060441887 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_13 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83626533713761 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288971064881 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨13, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83626533713761 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288971064881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_14 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83591786969327 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288975072073 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨14, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83591786969327 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288975072073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_15 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (41778532414939 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144489549029 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨15, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (41778532414939 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144489549029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_16 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83522367261047 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288983090723 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨16, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83522367261047 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288983090723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_17 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (20871923557161 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572246763949 / 25000000000000 : ℝ))
      (E := (cell12409 ⟨17, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (20871923557161 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572246763949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_18 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83453045698657 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144495528481 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨18, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83453045698657 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144495528481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_19 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83418421637251 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288995041303 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨19, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83418421637251 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2288995041303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12410_0 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (42040240284033 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288783360597 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨0, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (42040240284033 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288783360597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_1 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (84045411079631 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572196832829 / 25000000000000 : ℝ))
      (E := (cell12410 ⟨1, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (84045411079631 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572196832829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_2 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (84010366659289 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (35762364617 / 1562500000000 : ℝ))
      (E := (cell12410 ⟨2, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (84010366659289 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (35762364617 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_3 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83975347270243 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (114439766237 / 5000000000000 : ℝ))
      (E := (cell12410 ⟨3, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83975347270243 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (114439766237 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_4 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83940352875889 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288799308217 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨4, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83940352875889 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288799308217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_5 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83905383439817 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (286100411851 / 12500000000000 : ℝ))
      (E := (cell12410 ⟨5, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83905383439817 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (286100411851 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_6 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83870438925809 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288807293141 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨6, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83870438925809 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288807293141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_7 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (20958879824459 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (228881131159 / 10000000000000 : ℝ))
      (E := (cell12410 ⟨7, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (20958879824459 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (228881131159 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_8 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83800624520061 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288815300303 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨8, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83800624520061 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288815300303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_9 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (2617679829901 / 3125000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288819267073 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨9, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (2617679829901 / 3125000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288819267073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_10 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (5233181835793 / 6250000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (45776465549 / 2000000000000 : ℝ))
      (E := (cell12410 ⟨10, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (5233181835793 / 6250000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (45776465549 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_11 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83696088932349 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (457765456151 / 20000000000000 : ℝ))
      (E := (cell12410 ⟨11, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83696088932349 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (457765456151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_12 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83661293200723 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288831284023 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨12, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83661293200723 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288831284023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_13 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83626522142901 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572208823509 / 25000000000000 : ℝ))
      (E := (cell12410 ⟨13, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83626522142901 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572208823509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_14 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83591775724153 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144419629613 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨14, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83591775724153 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144419629613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_15 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (41778526954967 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288843243941 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨15, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (41778526954967 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288843243941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_16 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (20880589166469 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288847254223 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨16, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (20880589166469 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288847254223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_17 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (8348768395779 / 10000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (228885123769 / 10000000000000 : ℝ))
      (E := (cell12410 ⟨17, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (8348768395779 / 10000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (228885123769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_18 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83453035751667 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (91554210321 / 4000000000000 : ℝ))
      (E := (cell12410 ⟨18, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83453035751667 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (91554210321 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_19 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (8341841201367 / 10000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288859262313 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨19, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (8341841201367 / 10000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288859262313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12411_0 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (42040232361883 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144323781091 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨0, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (42040232361883 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144323781091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_1 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (21011348891753 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144325798341 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨1, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (21011348891753 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144325798341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_2 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (84010351477881 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288655549819 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨2, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (84010351477881 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288655549819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_3 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83975332419577 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288659546629 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨3, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83975332419577 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288659546629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_4 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83940338355497 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (286082942307 / 12500000000000 : ℝ))
      (E := (cell12411 ⟨4, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83940338355497 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (286082942307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_5 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83905369249231 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457733506837 / 20000000000000 : ℝ))
      (E := (cell12411 ⟨5, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83905369249231 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457733506837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_6 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41935212532281 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457734308489 / 20000000000000 : ℝ))
      (E := (cell12411 ⟨6, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41935212532281 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457734308489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_7 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (16767101153093 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144337785803 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨7, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (16767101153093 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144337785803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_8 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (838006113161 / 1000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288679513851 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨8, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (838006113161 / 1000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288679513851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_9 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83765741680819 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288683550871 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨9, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83765741680819 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288683550871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_10 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (523318105151 / 625000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144343758151 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨10, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (523318105151 / 625000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144343758151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_11 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (16739215342169 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457738306687 / 20000000000000 : ℝ))
      (E := (cell12411 ⟨11, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (16739215342169 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457738306687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_12 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83661281305783 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288695551311 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨12, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83661281305783 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288695551311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_13 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (16725302114813 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288699518631 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨13, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (16725302114813 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288699518631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_14 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (20897941120241 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (35760992187 / 1562500000000 : ℝ))
      (E := (cell12411 ⟨14, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (20897941120241 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (35760992187 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_15 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83557042991933 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (228870750161 / 10000000000000 : ℝ))
      (E := (cell12411 ⟨15, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83557042991933 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (228870750161 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_16 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (2610073314769 / 3125000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572177882399 / 25000000000000 : ℝ))
      (E := (cell12411 ⟨16, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (2610073314769 / 3125000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572177882399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_17 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (104359592111 / 125000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288715473367 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨17, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (104359592111 / 125000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288715473367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_18 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83453025806499 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144359756469 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨18, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83453025806499 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144359756469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_19 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83418402391871 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572180869753 / 25000000000000 : ℝ))
      (E := (cell12411 ⟨19, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83418402391871 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572180869753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12412_0 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (42040224441011 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (114425593711 / 5000000000000 : ℝ))
      (E := (cell12412 ⟨0, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (42040224441011 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (114425593711 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_1 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (21011345014227 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144257928491 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨1, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (21011345014227 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144257928491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_2 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (84010336298947 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288519874781 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨2, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (84010336298947 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288519874781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_3 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (5248457348209 / 6250000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288523879239 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨3, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (5248457348209 / 6250000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288523879239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_4 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (10492540479687 / 12500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (143032992469 / 6250000000000 : ℝ))
      (E := (cell12412 ⟨4, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (10492540479687 / 12500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (143032992469 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_5 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (16781071012199 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288531884461 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨5, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (16781071012199 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288531884461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_6 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41935205602813 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144267922407 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨6, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41935205602813 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144267922407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_7 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41917746117681 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (228853982681 / 10000000000000 : ℝ))
      (E := (cell12412 ⟨7, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41917746117681 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (228853982681 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_8 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83800598114367 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288543838563 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨8, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83800598114367 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288543838563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_9 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (5235358050437 / 6250000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144273914971 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨9, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (5235358050437 / 6250000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144273914971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_10 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41865442138889 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144275904241 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨10, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41865442138889 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144275904241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_11 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83696064491447 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288555839507 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨11, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83696064491447 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288555839507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_12 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20915317353227 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288559813997 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨12, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20915317353227 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288559813997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_13 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41813249503627 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (9154255187 / 400000000000 : ℝ))
      (E := (cell12412 ⟨13, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41813249503627 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (9154255187 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_14 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41795876619879 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288567794299 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨14, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41795876619879 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288567794299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_15 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20889258018969 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288571812933 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨15, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20889258018969 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288571812933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_16 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83522335481243 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144287900267 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨16, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83522335481243 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144287900267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_17 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (10435957927709 / 12500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288579821007 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨17, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (10435957927709 / 12500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288579821007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_18 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83453015863153 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (22885838217 / 1000000000000 : ℝ))
      (E := (cell12412 ⟨18, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83453015863153 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (22885838217 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_19 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41709196385927 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (45771756157 / 2000000000000 : ℝ))
      (E := (cell12412 ⟨19, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41709196385927 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (45771756157 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12413_0 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (16816086608567 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288376238931 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨0, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (16816086608567 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288376238931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_1 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (84045364549319 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144190113913 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨1, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (84045364549319 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144190113913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_2 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (84010321122487 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572096063137 / 25000000000000 : ℝ))
      (E := (cell12413 ⟨2, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (84010321122487 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572096063137 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_3 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41987651362771 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288388206871 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨3, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41987651362771 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288388206871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_4 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (16788061864377 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288392215617 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨4, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (16788061864377 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288392215617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_5 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83905340875109 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144198114921 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨5, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83905340875109 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144198114921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_6 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41935198674499 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288400200253 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨6, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41935198674499 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288400200253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_7 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83835478707527 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288404193093 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨7, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83835478707527 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288404193093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_8 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83800584914861 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (91536328659 / 4000000000000 : ℝ))
      (E := (cell12413 ⟨8, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83800584914861 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (91536328659 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_9 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (10470714491919 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288412220269 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨9, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (10470714491919 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288412220269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_10 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83730871733541 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286052026501 / 12500000000000 : ℝ))
      (E := (cell12413 ⟨10, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83730871733541 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286052026501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_11 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83696052274153 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (35756565609 / 1562500000000 : ℝ))
      (E := (cell12413 ⟨11, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83696052274153 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (35756565609 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_12 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83661257522097 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (457684837641 / 20000000000000 : ℝ))
      (E := (cell12413 ⟨12, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83661257522097 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (457684837641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_13 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41813243721233 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288428186479 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨13, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41813243721233 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288428186479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_14 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (10448967750067 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288432200329 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨14, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (10448967750067 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288432200329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_15 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41778510580881 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288436177911 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨15, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41778510580881 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288436177911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_16 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83522324891781 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288440183347 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨16, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83522324891781 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288440183347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_17 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41743826578203 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144222082127 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨17, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41743826578203 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144222082127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_18 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83453005921629 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286056023039 / 12500000000000 : ℝ))
      (E := (cell12413 ⟨18, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83453005921629 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286056023039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_19 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83418383153619 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286056516547 / 12500000000000 : ℝ))
      (E := (cell12413 ⟨19, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83418383153619 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286056516547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12414_0 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (42040208603101 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288240656321 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨0, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (42040208603101 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288240656321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_1 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (21011337261061 / 25000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288244651413 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨1, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (21011337261061 / 25000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288244651413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_2 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (84010305948499 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572062170781 / 25000000000000 : ℝ))
      (E := (cell12414 ⟨2, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (84010305948499 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572062170781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_3 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83975287882173 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144126322613 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨3, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83975287882173 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144126322613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_4 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41970147404333 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144128331271 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨4, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41970147404333 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144128331271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_5 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (20976331672893 / 25000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288260628229 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨5, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (20976331672893 / 25000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288260628229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_6 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41935191747339 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288264608763 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨6, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41935191747339 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288264608763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_7 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83835465181959 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (71508394141 / 3125000000000 : ℝ))
      (E := (cell12414 ⟨7, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83835465181959 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (71508394141 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_8 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83800571717581 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (228827264759 / 10000000000000 : ℝ))
      (E := (cell12414 ⟨8, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83800571717581 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (228827264759 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_9 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41882851532949 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288276605871 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨9, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41882851532949 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288276605871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_10 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (1674617183829 / 2000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (45765612217 / 2000000000000 : ℝ))
      (E := (cell12414 ⟨10, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (1674617183829 / 2000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (45765612217 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_11 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (20924010014741 / 25000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288284611841 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨11, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (20924010014741 / 25000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288284611841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_12 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83661245633349 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288288615877 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨12, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83661245633349 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288288615877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_13 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41813237939851 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (457658525947 / 20000000000000 : ℝ))
      (E := (cell12414 ⟨13, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41813237939851 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (457658525947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_14 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (2612241586353 / 3125000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572074150461 / 25000000000000 : ℝ))
      (E := (cell12414 ⟨14, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (2612241586353 / 3125000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572074150461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_15 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (8355701024959 / 10000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288300596547 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨15, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (8355701024959 / 10000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288300596547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_16 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (4176115715211 / 5000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (35754758777 / 1562500000000 : ℝ))
      (E := (cell12414 ⟨16, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (4176115715211 / 5000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (35754758777 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_17 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83487642893001 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (286038570161 / 12500000000000 : ℝ))
      (E := (cell12414 ⟨17, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83487642893001 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (286038570161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_18 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83452995981927 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (286039075097 / 12500000000000 : ℝ))
      (E := (cell12414 ⟨18, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83452995981927 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (286039075097 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_19 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (16683674707433 / 20000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144158284523 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨19, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (16683674707433 / 20000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144158284523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12415_0 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (21020100343031 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572026281597 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨0, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (21020100343031 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572026281597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_1 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (42022666770841 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288109127743 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨1, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (42022666770841 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288109127743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_2 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (84010290776983 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144056554341 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨2, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (84010290776983 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144056554341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_3 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41987636520617 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144058568229 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨3, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41987636520617 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144058568229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_4 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (20985070074459 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457624220907 / 20000000000000 : ℝ))
      (E := (cell12415 ⟨4, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (20985070074459 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457624220907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_5 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (16781062502077 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288125137519 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨5, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (16781062502077 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288125137519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_6 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41935184821333 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457625825653 / 20000000000000 : ℝ))
      (E := (cell12415 ⟨6, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41935184821333 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457625825653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_7 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83835451658659 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572033271267 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨7, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83835451658659 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572033271267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_8 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (2618767453829 / 3125000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288137073939 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨8, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (2618767453829 / 3125000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288137073939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_9 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83765690198629 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288141102733 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨9, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83765690198629 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288141102733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_10 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83730846651503 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144072560521 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨10, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83730846651503 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144072560521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_11 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41848013922939 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288149078107 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨11, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41848013922939 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288149078107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_12 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (16732246749333 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572038274253 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨12, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (16732246749333 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572038274253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_13 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (1045330803987 / 1250000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288157068437 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨13, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (1045330803987 / 1250000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288157068437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_14 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83591719528039 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (286020132119 / 12500000000000 : ℝ))
      (E := (cell12415 ⟨14, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83591719528039 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (286020132119 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_15 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (522231245871 / 625000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144082534421 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨15, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (522231245871 / 625000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144082534421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_16 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83522303718561 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572042262997 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨16, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83522303718561 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572042262997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_17 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41743816315729 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (228817307029 / 10000000000000 : ℝ))
      (E := (cell12415 ⟨17, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41743816315729 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (228817307029 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_18 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (16690597208809 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457635414219 / 20000000000000 : ℝ))
      (E := (cell12415 ⟨18, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (16690597208809 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457635414219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_19 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (20854590980623 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144090529817 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨19, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (20854590980623 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144090529817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12416_0 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (420401927703 / 500000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1143984853457 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨0, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (420401927703 / 500000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1143984853457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_1 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (84045318041633 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1143986828409 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨1, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (84045318041633 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1143986828409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_2 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (84010275607939 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1143988822439 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨2, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (84010275607939 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1143988822439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_3 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (3359010328109 / 4000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1143990840283 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨3, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (3359010328109 / 4000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1143990840283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_4 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (16788053157879 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (4468721987 / 195312500000 : ℝ))
      (E := (cell12416 ⟨4, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (16788053157879 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (4468721987 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_5 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (16781059666309 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (7149967631 / 312500000000 : ℝ))
      (E := (cell12416 ⟨5, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (16781059666309 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (7149967631 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_6 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (41935177896481 / 50000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2287993642919 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨6, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (41935177896481 / 50000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2287993642919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_7 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (10479429767203 / 12500000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (571999417177 / 25000000000000 : ℝ))
      (E := (cell12416 ⟨7, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (10479429767203 / 12500000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (571999417177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_8 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (838005453297 / 1000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288001611459 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨8, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (838005453297 / 1000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288001611459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_9 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (10470709666693 / 12500000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (457601130573 / 20000000000000 : ℝ))
      (E := (cell12416 ⟨9, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (10470709666693 / 12500000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (457601130573 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_10 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (837308341137 / 1000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288009626553 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨10, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (837308341137 / 1000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288009626553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_11 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (5231000977181 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288013597771 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨11, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (5231000977181 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288013597771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_12 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (20915305465511 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288017631611 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨12, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (20915305465511 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288017631611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_13 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (1045330659503 / 1250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288021618753 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨13, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (1045330659503 / 1250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288021618753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_14 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83591708294763 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572006405941 / 25000000000000 : ℝ))
      (E := (cell12416 ⟨14, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83591708294763 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572006405941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_15 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83556988431071 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288029594797 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨15, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83556988431071 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288029594797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_16 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83522293134803 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572008398993 / 25000000000000 : ℝ))
      (E := (cell12416 ⟨16, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83522293134803 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572008398993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_17 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (1304494099559 / 1562500000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144018787451 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨17, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (1304494099559 / 1562500000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144018787451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_18 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (5215811006749 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144020797633 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨18, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (5215811006749 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144020797633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_19 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83418354309599 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288045604141 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨19, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83418354309599 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288045604141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12417_0 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (84080369711629 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143917141171 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨0, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (84080369711629 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143917141171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_1 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (2626415704503 / 3125000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457567659289 / 20000000000000 : ℝ))
      (E := (cell12417 ⟨1, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (2626415704503 / 3125000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457567659289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_2 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (16802052088273 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457568458343 / 20000000000000 : ℝ))
      (E := (cell12417 ⟨2, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (16802052088273 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457568458343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_3 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41987621683323 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287846277553 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨3, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41987621683323 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287846277553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_4 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83940251283343 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287850263097 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨4, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83940251283343 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287850263097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_5 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83905284155053 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287854257229 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨5, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83905284155053 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287854257229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_6 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (20967585486391 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287858268571 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨6, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (20967585486391 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287858268571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_7 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (10479428077357 / 12500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287862247543 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨7, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (10479428077357 / 12500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287862247543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_8 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83800532139097 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457573252031 / 20000000000000 : ℝ))
      (E := (cell12417 ⟨8, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83800532139097 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457573252031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_9 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (20941416117661 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (571967564067 / 25000000000000 : ℝ))
      (E := (cell12417 ⟨9, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (20941416117661 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (571967564067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_10 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83730821578041 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457574848683 / 20000000000000 : ℝ))
      (E := (cell12417 ⟨10, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83730821578041 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457574848683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_11 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83696003426017 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (571969557219 / 25000000000000 : ℝ))
      (E := (cell12417 ⟨11, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83696003426017 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (571969557219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_12 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (16732241995897 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287882219679 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨12, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (16732241995897 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287882219679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_13 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83626441203543 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287886222601 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨13, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83626441203543 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287886222601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_14 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83591697063469 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457578037213 / 20000000000000 : ℝ))
      (E := (cell12417 ⟨14, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83591697063469 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457578037213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_15 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83556977524723 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287894232547 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨15, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83556977524723 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287894232547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_16 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (16704456510589 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457579638737 / 20000000000000 : ℝ))
      (E := (cell12417 ⟨16, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (16704456510589 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (457579638737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_17 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83487612113953 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287902191487 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨17, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83487612113953 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287902191487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_18 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83452966173743 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (142994135831 / 6250000000000 : ℝ))
      (E := (cell12417 ⟨18, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83452966173743 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (142994135831 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_19 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41709172349243 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (228791020257 / 10000000000000 : ℝ))
      (E := (cell12417 ⟨19, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41709172349243 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (228791020257 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12418_0 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (84080353885211 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287698910451 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨0, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (84080353885211 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287698910451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_1 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (8404528704907 / 10000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (457540586203 / 20000000000000 : ℝ))
      (E := (cell12418 ⟨1, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (8404528704907 / 10000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (457540586203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_2 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (42005122638631 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143853466769 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨2, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (42005122638631 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143853466769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_3 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83975228532997 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143855463709 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨3, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83975228532997 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143855463709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_4 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83940236779679 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (457542984359 / 20000000000000 : ℝ))
      (E := (cell12418 ⟨4, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83940236779679 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (457542984359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_5 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (20976317495227 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (571929731387 / 25000000000000 : ℝ))
      (E := (cell12418 ⟨5, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (20976317495227 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (571929731387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_6 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (10483791012559 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287722889377 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨6, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (10483791012559 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287722889377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_7 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83835411102353 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (14298292997 / 625000000000 : ℝ))
      (E := (cell12418 ⟨7, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83835411102353 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (14298292997 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_8 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41900259475359 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287730904089 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨8, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41900259475359 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287730904089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_9 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (10470706451241 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287734854951 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨9, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (10470706451241 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287734854951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_10 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (3349232361781 / 4000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (5719347139 / 250000000000 : ℝ))
      (E := (cell12418 ⟨10, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (3349232361781 / 4000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (5719347139 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_11 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (2092399780481 / 2500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (457548571069 / 20000000000000 : ℝ))
      (E := (cell12418 ⟨11, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (2092399780481 / 2500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (457548571069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_12 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83661198098987 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143873430607 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨12, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83661198098987 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143873430607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_13 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41813214824433 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143875439991 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨13, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41813214824433 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143875439991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_14 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (16718337166831 / 20000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285969357509 / 12500000000000 : ℝ))
      (E := (cell12418 ⟨14, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (16718337166831 / 20000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285969357509 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_15 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (16711393324063 / 20000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287758865827 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨15, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (16711393324063 / 20000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287758865827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_16 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (20880567993247 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (571940711281 / 25000000000000 : ℝ))
      (E := (cell12418 ⟨16, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (20880567993247 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (571940711281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_17 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83487601857991 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143883430931 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨17, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83487601857991 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143883430931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_18 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83452956241321 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285971357923 / 12500000000000 : ℝ))
      (E := (cell12418 ⟨18, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83452956241321 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285971357923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_19 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (162926435721 / 195312500000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (57194371373 / 2500000000000 : ℝ))
      (E := (cell12418 ⟨19, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (162926435721 / 195312500000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (57194371373 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12419_0 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (16816067612269 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (91502545961 / 4000000000000 : ℝ))
      (E := (cell12419 ⟨0, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (16816067612269 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (91502545961 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_1 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (16809054311311 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (71486488073 / 3125000000000 : ℝ))
      (E := (cell12419 ⟨1, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (16809054311311 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (71486488073 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_2 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (21002557528907 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (142973226761 / 6250000000000 : ℝ))
      (E := (cell12419 ⟨2, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (21002557528907 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (142973226761 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_3 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (5248450856361 / 6250000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457515126033 / 20000000000000 : ℝ))
      (E := (cell12419 ⟨3, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (5248450856361 / 6250000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457515126033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_4 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83940222278403 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (14297372709 / 625000000000 : ℝ))
      (E := (cell12419 ⟨4, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83940222278403 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (14297372709 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_5 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (8390525580911 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287583588981 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨5, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (8390525580911 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287583588981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_6 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41935157128843 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143793810591 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨6, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41935157128843 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143793810591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_7 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41917698794057 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143795811293 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨7, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41917698794057 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143795811293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_8 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (20950126441141 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287595601231 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨8, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (20950126441141 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287595601231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_9 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41882819375697 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571899905723 / 25000000000000 : ℝ))
      (E := (cell12419 ⟨9, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41882819375697 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571899905723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_10 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (1674615930263 / 2000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (114380178957 / 5000000000000 : ℝ))
      (E := (cell12419 ⟨10, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (1674615930263 / 2000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (114380178957 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_11 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (20923994753641 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287607593257 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨11, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (20923994753641 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287607593257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_12 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83661186220551 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143805778109 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨12, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83661186220551 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143805778109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_13 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (8362641809621 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143807795449 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨13, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (8362641809621 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143807795449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_14 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41795837303411 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287619587679 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨14, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41795837303411 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287619587679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_15 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83556955717847 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571905888193 / 25000000000000 : ℝ))
      (E := (cell12419 ⟨15, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83556955717847 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571905888193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_16 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83522261394929 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287627550293 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨16, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83522261394929 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287627550293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_17 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83487591603887 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287631586033 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨17, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83487591603887 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287631586033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_18 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83452946310719 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287635549129 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨18, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83452946310719 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287635549129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_19 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83418325481597 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457527912239 / 20000000000000 : ℝ))
      (E := (cell12419 ⟨19, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83418325481597 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457527912239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12420_0 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (84080322240031 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287428382503 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨0, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (84080322240031 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287428382503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_1 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (84045256066551 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287432416211 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨1, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (84045256066551 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287432416211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_2 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (5250638434779 / 6250000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287436375631 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨2, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (5250638434779 / 6250000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287436375631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_3 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41987599436491 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (457488077159 / 20000000000000 : ℝ))
      (E := (cell12420 ⟨3, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41987599436491 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (457488077159 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_4 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41970103889757 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (142965274877 / 6250000000000 : ℝ))
      (E := (cell12420 ⟨4, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41970103889757 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (142965274877 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_5 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83905241639657 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143724181663 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨5, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83905241639657 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143724181663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_6 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (16774060083441 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143726203033 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨6, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (16774060083441 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143726203033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_7 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83835384076139 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287456360851 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨7, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83835384076139 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287456360851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_8 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (10475061572579 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (71483135987 / 3125000000000 : ℝ))
      (E := (cell12420 ⟨8, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (10475061572579 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (71483135987 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_9 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83765625895043 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287464386117 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨9, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83765625895043 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287464386117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_10 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41865391991959 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (114373417801 / 5000000000000 : ℝ))
      (E := (cell12420 ⟨10, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41865391991959 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (114373417801 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_11 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (8369596681199 / 10000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (91498895383 / 4000000000000 : ℝ))
      (E := (cell12420 ⟨11, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (8369596681199 / 10000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (91498895383 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_12 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (5228823396511 / 6250000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143738181377 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨12, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (5228823396511 / 6250000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143738181377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_13 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41813203272787 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (45749607107 / 2000000000000 : ℝ))
      (E := (cell12420 ⟨13, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41813203272787 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (45749607107 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_14 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (20897915845367 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287484368887 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨14, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (20897915845367 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287484368887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_15 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83556944817319 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143744175757 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨15, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83556944817319 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143744175757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_16 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (8352225081877 / 10000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285936538649 / 12500000000000 : ℝ))
      (E := (cell12420 ⟨16, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (8352225081877 / 10000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285936538649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_17 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83487581351643 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287496305819 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨17, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83487581351643 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287496305819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_18 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (16690587276387 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285937543367 / 12500000000000 : ℝ))
      (E := (cell12420 ⟨18, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (16690587276387 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285937543367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_19 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83418315875821 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287504321393 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨19, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83418315875821 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287504321393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12421_0 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (84080306421267 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287293226451 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨0, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (84080306421267 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287293226451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_1 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (5252827536191 / 6250000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457459441807 / 20000000000000 : ℝ))
      (E := (cell12421 ⟨1, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (5252827536191 / 6250000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457459441807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_2 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (10501274974971 / 12500000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287301233733 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨2, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (10501274974971 / 12500000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287301233733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_3 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83975184046617 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (571826298577 / 25000000000000 : ℝ))
      (E := (cell12421 ⟨3, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83975184046617 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (571826298577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_4 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (8394019328301 / 10000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (285913651947 / 12500000000000 : ℝ))
      (E := (cell12421 ⟨4, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (8394019328301 / 10000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (285913651947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_5 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (1678104549451 / 2000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143656595343 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨5, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (1678104549451 / 2000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143656595343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_6 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (20967571644757 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287317186109 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨6, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (20967571644757 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287317186109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_7 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (20958842641607 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287321210207 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨7, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (20958842641607 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287321210207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_8 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83800479398923 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287325213117 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨8, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83800479398923 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287325213117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_9 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41882806520437 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143664601309 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨9, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41882806520437 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143664601309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_10 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83730771456827 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143666593121 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨10, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83730771456827 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143666593121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_11 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83695954611517 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287337171261 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨11, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83695954611517 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287337171261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_12 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (4183058123493 / 5000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143670582351 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨12, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (4183058123493 / 5000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143670582351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_13 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41813197498479 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143672586669 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨13, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41813197498479 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143672586669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_14 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83591652158093 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (571837286397 / 25000000000000 : ℝ))
      (E := (cell12421 ⟨14, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83591652158093 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (571837286397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_15 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83556933918729 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287353145791 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨15, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83556933918729 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287353145791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_16 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (8352224024451 / 10000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (114367858999 / 5000000000000 : ℝ))
      (E := (cell12421 ⟨16, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (8352224024451 / 10000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (114367858999 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_17 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83487571101257 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287361137581 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨17, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83487571101257 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287361137581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_18 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83452926454969 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287365140403 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨18, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83452926454969 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287365140403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_19 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41709153135911 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143684567759 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨19, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41709153135911 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143684567759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12422_0 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (42040145302527 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143579061543 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨0, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (42040145302527 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143579061543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_1 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (8404522509407 / 10000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143581056209 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨1, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (8404522509407 / 10000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143581056209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_2 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (4200509232277 / 5000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287166086827 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨2, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (4200509232277 / 5000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287166086827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_3 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41987584611339 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287170113559 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨3, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41987584611339 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287170113559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_4 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83940178788893 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228717408607 / 10000000000000 : ℝ))
      (E := (cell12422 ⟨4, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83940178788893 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228717408607 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_5 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83905213307787 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457435614213 / 20000000000000 : ℝ))
      (E := (cell12422 ⟨5, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83905213307787 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457435614213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_6 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (16774054548631 / 20000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143591038579 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨6, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (16774054548631 / 20000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143591038579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_7 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (4191767852949 / 5000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (285898264089 / 12500000000000 : ℝ))
      (E := (cell12422 ⟨7, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (4191767852949 / 5000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (285898264089 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_8 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83800466219437 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143595034947 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨8, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83800466219437 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143595034947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_9 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41882800094443 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287194072399 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨9, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41882800094443 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287194072399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_10 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83730758931877 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (142949879363 / 6250000000000 : ℝ))
      (E := (cell12422 ⟨10, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83730758931877 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (142949879363 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_11 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (10461992801643 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457440413879 / 20000000000000 : ℝ))
      (E := (cell12422 ⟨11, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (10461992801643 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457440413879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_12 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (16732230119521 / 20000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457441215637 / 20000000000000 : ℝ))
      (E := (cell12422 ⟨12, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (16732230119521 / 20000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457441215637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_13 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83626383450361 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287210044867 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨13, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83626383450361 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287210044867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_14 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83591640936697 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287214034003 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨14, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83591640936697 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287214034003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_15 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41778461511039 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228721805187 / 10000000000000 : ℝ))
      (E := (cell12422 ⟨15, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41778461511039 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228721805187 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_16 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83522229672147 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143611023173 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨16, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83522229672147 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143611023173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_17 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (10435945106591 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287226023143 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨17, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (10435945106591 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287226023143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_18 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83452916529821 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (142951877871 / 6250000000000 : ℝ))
      (E := (cell12422 ⟨18, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83452916529821 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (142951877871 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_19 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41709148334801 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287234061797 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨19, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41709148334801 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287234061797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12423_0 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (84080274791391 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571755768103 / 25000000000000 : ℝ))
      (E := (cell12423 ⟨0, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (84080274791391 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571755768103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_1 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (84045209611593 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287027068557 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨1, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (84045209611593 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287027068557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_2 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (84010169493779 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287031050571 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨2, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (84010169493779 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287031050571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_3 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (16795030880233 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287035027847 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨3, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (16795030880233 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287035027847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_4 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (2098504107429 / 2500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143519533697 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨4, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (2098504107429 / 2500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143519533697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_5 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (83905199145369 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287043062359 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨5, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (83905199145369 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287043062359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_6 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (16774051781917 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (228704702129 / 10000000000000 : ℝ))
      (E := (cell12423 ⟨6, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (16774051781917 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (228704702129 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_7 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (16767068710759 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (114352550521 / 5000000000000 : ℝ))
      (E := (cell12423 ⟨7, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (16767068710759 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (114352550521 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_8 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (20950113260543 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (457411007571 / 20000000000000 : ℝ))
      (E := (cell12423 ⟨8, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (20950113260543 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (457411007571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_9 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (2094139683477 / 2500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143529497729 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨9, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (2094139683477 / 2500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143529497729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_10 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (20932686602267 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143531503359 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨10, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (20932686602267 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143531503359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_11 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (8369593021687 / 10000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (114353351047 / 5000000000000 : ℝ))
      (E := (cell12423 ⟨11, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (8369593021687 / 10000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (114353351047 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_12 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (5228821170463 / 6250000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143535493541 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨12, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (5228821170463 / 6250000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143535493541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_13 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (83626371905783 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287075028021 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨13, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (83626371905783 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287075028021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_14 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (522447685733 / 625000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143539488011 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨14, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (522447685733 / 625000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143539488011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_15 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (16711382425473 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287083011619 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨15, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (16711382425473 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287083011619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_16 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (41761109550841 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143543483223 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨16, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (41761109550841 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143543483223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_17 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (83487550606057 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (285886370313 / 12500000000000 : ℝ))
      (E := (cell12423 ⟨17, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (83487550606057 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (285886370313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_18 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (8345290660649 / 10000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143547502667 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨18, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (8345290660649 / 10000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143547502667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_19 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (41709143534579 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (114354949189 / 5000000000000 : ℝ))
      (E := (cell12423 ⟨19, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (41709143534579 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (114354949189 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12424_0 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (21020064745069 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286888074429 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨0, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (21020064745069 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286888074429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_1 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (84045194131623 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143446038727 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨1, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (84045194131623 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143446038727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_2 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (21002538586121 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286896067139 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨2, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (21002538586121 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286896067139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_3 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83975139582077 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143450026437 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨3, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83975139582077 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143450026437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_4 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83940149807813 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457380808759 / 20000000000000 : ℝ))
      (E := (cell12424 ⟨4, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83940149807813 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457380808759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_5 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41952592492647 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (91476321951 / 4000000000000 : ℝ))
      (E := (cell12424 ⟨5, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41952592492647 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (91476321951 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_6 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41935122539159 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286912018507 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨6, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41935122539159 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286912018507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_7 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83835330050871 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (285864502403 / 12500000000000 : ℝ))
      (E := (cell12424 ⟨7, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83835330050871 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (285864502403 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_8 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (10475054983391 / 12500000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286920001063 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨8, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (10475054983391 / 12500000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286920001063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_9 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41882787245727 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286924029791 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨9, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41882787245727 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286924029791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_10 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83730733888397 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (142932999811 / 6250000000000 : ℝ))
      (E := (cell12424 ⟨10, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83730733888397 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (142932999811 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_11 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (10461989752837 / 12500000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457386405179 / 20000000000000 : ℝ))
      (E := (cell12424 ⟨11, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (10461989752837 / 12500000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457386405179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_12 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (8366112685927 / 10000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143468003759 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨12, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (8366112685927 / 10000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143468003759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_13 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83626360363223 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (228694000663 / 10000000000000 : ℝ))
      (E := (cell12424 ⟨13, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83626360363223 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (228694000663 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_14 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (65305951953 / 78125000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (35733499557 / 1562500000000 : ℝ))
      (E := (cell12424 ⟨14, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (65305951953 / 78125000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (35733499557 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_15 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83556901234589 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (28586850313 / 1250000000000 : ℝ))
      (E := (cell12424 ⟨15, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83556901234589 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (28586850313 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_16 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (16704441706623 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143475999219 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨16, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (16704441706623 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143475999219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_17 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83487540361243 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457391202769 / 20000000000000 : ℝ))
      (E := (cell12424 ⟨17, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83487540361243 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457391202769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_18 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (3338115867399 / 4000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143479980197 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨18, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (3338115867399 / 4000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143479980197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_19 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (8341827747049 / 10000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286963959693 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨19, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (8341827747049 / 10000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286963959693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

end BstLean.Part268
